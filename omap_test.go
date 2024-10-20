// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build go1.23

package omap

import (
	"bytes"
	"cmp"
	"fmt"
	"iter"
	"math"
	"math/rand/v2"
	"slices"
	"testing"
)

type Interface[K, V any] interface {
	All() iter.Seq2[K, V]
	Backward() iter.Seq2[K, V]
	Delete(key K) bool
	Get(key K) (V, bool)
	Set(key K, val V) (V, bool)
	Min() (K, bool)
	Max() (K, bool)
	Len() int
	At(int) (K, V)
	root() **node[K, V]
}

func permute(m Interface[int, int], n int) (perm, slice []int) {
	perm = rand.Perm(n)
	slice = make([]int, 2*n+1)
	for i, x := range perm {
		m.Set(2*x+1, i+1)
		slice[2*x+1] = i + 1
	}
	// Overwrite-Set half the entries.
	for i, x := range perm[:len(perm)/2] {
		m.Set(2*x+1, i+100)
		slice[2*x+1] = i + 100
	}
	return perm, slice
}

func dump(m Interface[int, int]) string {
	var buf bytes.Buffer
	var walk func(*node[int, int])
	walk = func(x *node[int, int]) {
		if x == nil {
			fmt.Fprintf(&buf, "nil")
			return
		}
		fmt.Fprintf(&buf, "(%d[%d] ", x.key, x._size)
		walk(x.left)
		fmt.Fprintf(&buf, " ")
		walk(x.right)
		fmt.Fprintf(&buf, ")")
	}
	walk(*m.root())
	return buf.String()
}

func test(t *testing.T, f func(*testing.T, func() Interface[int, int])) {
	t.Run("Map", func(t *testing.T) {
		f(t, func() Interface[int, int] { return new(Map[int, int]) })
	})
	t.Run("MapFunc", func(t *testing.T) {
		f(t, func() Interface[int, int] { return NewMapFunc[int, int](cmp.Compare) })
	})
}

func TestGet(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			m := newMap()
			_, slice := permute(m, N)
			for k, want := range slice {
				v, ok := m.Get(k)
				if v != want || ok != (want > 0) {
					t.Fatalf("Get(%d) = %d, %v, want %d, %v\nM: %v", k, v, ok, want, want > 0, dump(m))
				}
			}
		}
	})
}

func TestSet(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		check := func(gotOld int, gotAdded bool) func(int, bool) {
			return func(wantOld int, wantAdded bool) {
				t.Helper()
				if gotOld != wantOld || gotAdded != wantAdded {
					t.Errorf("got %d, %t, want %d, %t", gotOld, gotAdded, wantOld, wantAdded)
				}
			}
		}

		m := newMap()
		check(m.Set(1, 10))(0, true)
		check(m.Set(2, 20))(0, true)
		check(m.Set(1, 5))(10, false)
		check(m.Set(1, 8))(5, false)
	})
}

func TestMin(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			m := newMap()
			permute(m, N)
			have, ok := m.Min()
			want := 1
			wok := true
			if N == 0 {
				want = 0
				wok = false
			}
			if have != want || ok != wok {
				t.Errorf("N=%d Min() returned %d, %t want %d, %t", N, have, ok, want, wok)
			}
		}
	})
}

func TestMax(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			m := newMap()
			permute(m, N)
			have, ok := m.Max()
			want := 2*N - 1
			wok := true
			if N == 0 {
				want = 0
				wok = false
			}
			if have != want || ok != wok {
				t.Errorf("N=%d Min() returned %d, %t want %d, %t", N, have, ok, want, wok)
			}
		}
	})
}

func TestAll(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			m := newMap()
			_, slice := permute(m, N)
			var have []int
			for k, v := range m.All() {
				if v != slice[k] {
					t.Errorf("All() returned %d, %d want %d, %d", k, v, k, slice[k])
				}
				have = append(have, k)
				if len(have) > N+5 { // too many; looping?
					break
				}
			}
			want := nonzeroIndexes(slice)
			if !slices.Equal(have, want) {
				t.Errorf("All() = %v, want %v", have, want)
			}
		}
	})
}

func TestBackward(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			m := newMap()
			_, slice := permute(m, N)
			var have []int
			for k, v := range m.Backward() {
				if v != slice[k] {
					t.Errorf("All() returned %d, %d want %d, %d", k, v, k, slice[k])
				}
				have = append(have, k)
				if len(have) > N+5 { // too many; looping?
					break
				}
			}
			want := nonzeroIndexes(slice)
			slices.Reverse(want)
			if !slices.Equal(have, want) {
				t.Errorf("All() = %v, want %v", have, want)
			}
		}
	})
}

func TestAllRange(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		check := func(m Interface[int, int], slice []int, blo, bhi bound[int]) {
			var have []int
			r := newRange(m, blo, bhi)
			for k, v := range r.All() {
				if v != slice[k] {
					t.Errorf("All() returned %d, %d want %d, %d", k, v, k, slice[k])
				}
				have = append(have, k)
				if len(have) > len(slice)+5 { // too many; looping?
					break
				}
			}
			var want []int
			for k, v := range slice {
				if v != 0 && in(k, blo, bhi) {
					want = append(want, k)
				}
			}
			if !slices.Equal(have, want) {
				t.Errorf("All() = %v, want %v", have, want)
			}
		}

		for N := range 11 {
			m := newMap()
			_, slice := permute(m, N)
			for hi := range slice {
				for _, bhi := range []bound[int]{including(hi), excluding(hi), inf()} {
					for lo := range hi + 1 {
						for _, blo := range []bound[int]{including(lo), excluding(lo), inf()} {
							check(m, slice, blo, bhi)
						}
					}
				}
			}
		}
	})
}

func TestBackwardRange(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		check := func(m Interface[int, int], slice []int, blo, bhi bound[int]) {
			var have []int
			r := newRange(m, blo, bhi)
			for k, v := range r.Backward() {
				if v != slice[k] {
					t.Errorf("Backward(%s) returned %d, %d want %d, %d", r, k, v, k, slice[k])
				}
				have = append(have, k)
				if len(have) > len(slice)+5 { // too many; looping?
					break
				}
			}
			var want []int
			for k, v := range slice {
				if v != 0 && in(k, blo, bhi) {
					want = append(want, k)
				}
			}
			slices.Reverse(want)
			if !slices.Equal(have, want) {
				t.Errorf("Backward(%s) = %v, want %v", r, have, want)
			}
		}

		for N := range 11 {
			m := newMap()
			_, slice := permute(m, N)
			for hi := range slice {
				for _, bhi := range []bound[int]{including(hi), excluding(hi), inf()} {
					for lo := range hi + 1 {
						for _, blo := range []bound[int]{including(lo), excluding(lo), inf()} {
							check(m, slice, blo, bhi)
						}
					}
				}
			}
		}
	})
}

func TestDelete(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		checkLen := func(m Interface[int, int], n int) {
			t.Helper()
			if m.Len() != n {
				t.Errorf("m.Len() = %d, want %d", m.Len(), n)
			}
		}

		for N := range 11 {
			m := newMap()
			checkLen(m, 0)
			_, slice := permute(m, N)
			checkLen(m, N)
			wantLen := N
			for _, x := range rand.Perm(len(slice)) {
				if m.Delete(x) {
					wantLen--
				}
				checkLen(m, wantLen)
				slice[x] = 0
				var have []int
				for k, _ := range m.All() {
					have = append(have, k)
				}
				want := nonzeroIndexes(slice)
				slices.Sort(want)
				if !slices.Equal(have, want) {
					t.Errorf("after Delete(%v), All() = %v, want %v", x, have, want)
				}
			}
		}
	})
}

func TestDeleteRange(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		check := func(N int, blo, bhi bound[int], clearReverse bool) {
			t.Helper()
			m := newMap()
			r := newRange(m, blo, bhi)
			_, slice := permute(m, N)
			if clearReverse {
				newRange(m, bhi, blo).Clear()
			}
			newRange(m, blo, bhi).Clear()
			var have []int
			for k, _ := range m.All() {
				have = append(have, k)
			}
			want := keep(slice, func(k int) bool { return !in(k, blo, bhi) })
			if !slices.Equal(have, want) {
				t.Errorf("N=%d, after Clear(%s), All() = %v, want %v", N, r, have, want)
			}
			if g, w := m.Len(), len(have); g != w {
				t.Errorf("m.Len() = %d, want %d", g, w)
			}
		}

		for N := range 11 {
			for hi := range 2*N + 1 {
				for _, bhi := range []bound[int]{including(hi), excluding(hi)} {
					for lo := range hi + 1 {
						for _, blo := range []bound[int]{including(lo), excluding(lo)} {
							check(N, blo, bhi, lo < hi)
						}
					}
				}
			}
			for x := range 2*N + 1 {
				check(N, including(x), inf(), false)
				check(N, excluding(x), inf(), false)
				check(N, inf(), including(x), false)
				check(N, inf(), excluding(x), false)
			}
			check(N, inf(), inf(), false)
		}
	})
}

func TestAllDeleteRange(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		var deleteLo, deleteHi int
		for _, mode := range []string{"prev", "current", "next", "clear"} {
			for N := range 8 {
				for target := 1; target <= 2*N-1; target += 2 {
					m := newMap()
					_, slice := permute(m, N)
					var have []int
					for k, _ := range m.All() {
						deleteLo, deleteHi = clearRange(m, true, k, target, mode, slice)
						have = append(have, k)
					}
					want := nonzeroIndexes(slice)
					if !slices.Equal(have, want) {
						t.Errorf("All() deleting range [%d, %d] at %d = %v, want %v", deleteLo, deleteHi, target, have, want)
					}
					checkSize(t, m.(omap[int, int]))
				}
			}
		}
	})
}

func TestBackwardDeleteRange(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for _, mode := range []string{"prev", "current", "next", "clear"} {
			for N := range 8 {
				for target := 1; target <= 2*N-1; target += 2 {
					m := newMap()
					_, slice := permute(m, N)
					var have []int
					var deleteLo, deleteHi int
					for k, _ := range m.Backward() {
						deleteLo, deleteHi = clearRange(m, false, k, target, mode, slice)
						have = append(have, k)
					}
					want := nonzeroIndexes(slice)
					slices.Reverse(want)
					if !slices.Equal(have, want) {
						t.Errorf("Backward() deleting range [%d, %d] at %d = %v, want %v", deleteLo, deleteHi, target, have, want)
					}
					checkSize(t, m.(omap[int, int]))
				}
			}
		}
	})
}

func clearRange(m Interface[int, int], forwards bool, k, target int, mode string, slice []int) (int, int) {
	var deleteLo, deleteHi int
	if k == target {
		switch mode {
		case "prev":
			deleteLo, deleteHi = k-5, k-1
		case "current":
			deleteLo, deleteHi = k-2, k+2
		case "next":
			deleteLo, deleteHi = k+1, k+5
		case "clear":
			deleteLo = math.MinInt
			deleteHi = math.MaxInt - 1
		}
		newRange(m, including(deleteLo), including(deleteHi)).Clear()
		var lo, hi int
		if forwards {
			lo = max(deleteLo, k+1)
			hi = min(len(slice), deleteHi+1)
		} else {
			lo = max(deleteLo, 0)
			hi = min(k, deleteHi+1)
		}
		for i := lo; i < hi; i++ {
			slice[i] = 0
		}
	}
	return deleteLo, deleteHi
}

func TestAt(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			m := newMap()
			_, slice := permute(m, N)
			var haveKeys, haveVals []int
			for i := 0; i < N; i++ {
				k, v := m.At(i)
				haveKeys = append(haveKeys, k)
				haveVals = append(haveVals, v)
			}
			var wantKeys, wantVals []int
			for k, v := range slice {
				if v != 0 {
					wantKeys = append(wantKeys, k)
					wantVals = append(wantVals, v)
				}
			}
			if !slices.Equal(haveKeys, wantKeys) {
				t.Errorf("keys: have %v, want %v", haveKeys, wantKeys)
			}
			if !slices.Equal(haveVals, wantVals) {
				t.Errorf("values: have %v, want %v", haveVals, wantVals)
			}
		}
	})
}

func checkSize[K, V any](t *testing.T, m omap[K, V]) {
	t.Helper()
	chsz(t, *m.root())
}

func chsz[K, V any](t *testing.T, x *node[K, V]) {
	t.Helper()
	if x == nil {
		return
	}
	chsz(t, x.left)
	chsz(t, x.right)
	if g, w := x._size, 1+x.left.size()+x.right.size(); g != w {
		t.Fatalf("checkSize key=%v: have %d, want %d", x.key, g, w)
	}
}

func TestRangeString(t *testing.T) {
	m := newMap(nil)
	for _, test := range []struct {
		r    iRange[int, int]
		want string
	}{
		{newRange(m, inf(), inf()), "(-∞, ∞)"},
		{newRange(m, including(1), inf()), "[1, ∞)"},
		{newRange(m, inf(), excluding(3)), "(-∞, 3)"},
		{newRange(m, including(1), including(3)), "[1, 3]"},
		{newRange(m, including(1), excluding(3)), "[1, 3)"},
		{newRange(m, excluding(1), including(3)), "(1, 3]"},
		{newRange(m, excluding(1), excluding(3)), "(1, 3)"},
	} {
		got := fmt.Sprint(test.r)
		if got != test.want {
			t.Errorf("%v: got %q, want %q", test.r, got, test.want)
		}
	}
}

type iRange[K, V any] interface {
	Clear()
	All() iter.Seq2[K, V]
	Backward() iter.Seq2[K, V]
}

func newRange[K cmp.Ordered, V any](m Interface[K, V], lo, hi bound[K]) iRange[K, V] {
	switch m := m.(type) {
	case *Map[K, V]:
		return Range[K, V]{m: m, _lo: lo, _hi: hi}
	case *MapFunc[K, V]:
		return RangeFunc[K, V]{m: m, _lo: lo, _hi: hi}
	default:
		panic("bad map type")
	}
}

func inf() bound[int] { return bound[int]{} }

func keep(s []int, f func(int) bool) []int {
	var r []int
	for k, v := range s {
		if v != 0 && f(k) {
			r = append(r, k)
		}
	}
	return r
}

func nonzeroIndexes(s []int) []int {
	var r []int
	for k, v := range s {
		if v != 0 {
			r = append(r, k)
		}
	}
	return r
}

// in reports whether n is within the interval specified by lo and hi.
func in(n int, lo, hi bound[int]) bool {
	if lo.present && ((lo.inclusive && n < lo.key) || (!lo.inclusive && n <= lo.key)) {
		return false
	}
	if hi.present && ((hi.inclusive && n > hi.key) || (!hi.inclusive && n >= hi.key)) {
		return false
	}
	return true
}

func TestIn(t *testing.T) {
	// N=5, after DeleteRange((-∞, 3]), All() = [], want [1]
	slice := []int{0, 1, 0, 3, 0, 5, 0, 7, 0, 9, 0, 11}
	var blo bound[int]
	bhi := including(3)
	t.Log(keep(slice, func(k int) bool { return !in(k, blo, bhi) }))
}
