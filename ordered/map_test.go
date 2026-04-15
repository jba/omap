// Copyright 2024 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ordered

import (
	"bytes"
	"cmp"
	"fmt"
	"iter"
	"maps"
	"math"
	"math/rand/v2"
	"reflect"
	"slices"
	"strings"
	"testing"
)

type Interface[K, V any] interface {
	All() iter.Seq2[K, V]
	Backward() iter.Seq2[K, V]
	Delete(key K) (V, bool)
	Get(key K) (V, bool)
	Set(key K, val V) (V, bool)
	Min() (K, V, bool)
	Max() (K, V, bool)
	Len() int
	Nth(int) (K, V)
	SetAll(iter.Seq2[K, V]) bool
	DeleteAll(iter.Seq[K]) bool
	String() string

	root() **node[K, V]
}

// a non-zero slice element v at index k corresponds
// with a map entry k:v.
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

func mstr(m Interface[int, int]) string {
	var buf bytes.Buffer
	buf.WriteByte('{')
	first := true
	for k, v := range m.All() {
		if !first {
			buf.WriteString(", ")
		}
		first = false
		fmt.Fprintf(&buf, "%d:%d", k, v)
	}
	buf.WriteByte('}')
	return buf.String()
}

func dump(m Interface[int, int]) string {
	var buf bytes.Buffer
	var walk func(*node[int, int])
	walk = func(x *node[int, int]) {
		if x == nil {
			fmt.Fprintf(&buf, "nil")
			return
		}
		fmt.Fprintf(&buf, "(%d[%d]=%d ", x.key, x._size, x.val)
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
		f(t, func() Interface[int, int] { return new(_OMap[int, int]) })
	})
	t.Run("MapFunc", func(t *testing.T) {
		f(t, func() Interface[int, int] { return NewMap[int, int](cmp.Compare) })
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

func TestAt(t *testing.T) {
	t.Run("OMap", func(t *testing.T) {
		var m _OMap[int, int]
		// Missing key returns zero
		if got := m.At(1); got != 0 {
			t.Errorf("At(1) on empty map: got %d, want 0", got)
		}
		m.Set(1, 10)
		m.Set(2, 20)
		// Existing key returns value
		if got := m.At(1); got != 10 {
			t.Errorf("At(1): got %d, want 10", got)
		}
		if got := m.At(2); got != 20 {
			t.Errorf("At(2): got %d, want 20", got)
		}
		// Missing key returns zero
		if got := m.At(3); got != 0 {
			t.Errorf("At(3): got %d, want 0", got)
		}
	})

	t.Run("Map", func(t *testing.T) {
		m := NewMap[int, int](cmp.Compare)
		// Missing key returns zero
		if got := m.At(1); got != 0 {
			t.Errorf("At(1) on empty map: got %d, want 0", got)
		}
		m.Set(1, 10)
		m.Set(2, 20)
		// Existing key returns value
		if got := m.At(1); got != 10 {
			t.Errorf("At(1): got %d, want 10", got)
		}
		if got := m.At(2); got != 20 {
			t.Errorf("At(2): got %d, want 20", got)
		}
		// Missing key returns zero
		if got := m.At(3); got != 0 {
			t.Errorf("At(3): got %d, want 0", got)
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

func TestSetAll(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		m := newMap()
		m.Set(0, 1)
		gotb := m.SetAll(slices.All([]int{1, 3, 5}))
		if !gotb {
			t.Fatal("got false, want true")
		}
		got := toMap(m)
		want := map[int]int{0: 1, 1: 3, 2: 5}
		if !maps.Equal(got, want) {
			t.Fatalf("got %v, want %v", got, want)
		}
	})
}

func TestDeleteAll(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		m := newMap()
		m.SetAll(slices.All([]int{1, 3, 5}))
		// keys are 0, 1, 2
		gotb := m.DeleteAll(slices.Values([]int{2, 3, 5}))
		if !gotb {
			t.Fatal("got false, want true")
		}

		got := toMap(m)
		want := map[int]int{0: 1, 1: 3}
		if !maps.Equal(got, want) {
			t.Fatalf("got %v, want %v", got, want)
		}
	})
}

func toMap(in Interface[int, int]) map[int]int {
	out := map[int]int{}
	for k, v := range in.All() {
		out[k] = v
	}
	return out
}

func TestMin(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			m := newMap()
			_, slice := permute(m, N)
			haveKey, haveVal, ok := m.Min()
			wantKey := 1
			var wantVal int
			var wok bool
			if N == 0 {
				wantKey = 0
				wantVal = 0
				wok = false
			} else {
				wantVal = slice[wantKey]
				wok = true
			}
			if haveKey != wantKey || haveVal != wantVal || ok != wok {
				t.Errorf("N=%d Min() returned %d, %t want %d, %t", N, haveKey, ok, wantKey, wok)
			}
		}
	})
}

func TestMax(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			m := newMap()
			_, slice := permute(m, N)
			haveKey, haveVal, ok := m.Max()
			wantKey := 2*N - 1
			var wantVal int
			var wok bool
			if N == 0 {
				wantKey = 0
				wantVal = 0
				wok = false
			} else {
				wantVal = slice[wantKey]
				wok = true
			}
			if haveKey != wantKey || haveVal != wantVal || ok != wok {
				t.Errorf("N=%d Max() returned %d, %t want %d, %t", N, haveKey, ok, wantKey, wok)
			}
		}
	})
}

func TestMinRange(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			for blo, bhi := range bounds(N) {
				m := newMap()
				_, slice := permute(m, N)
				r := newMapSpan(m, blo, bhi)
				haveKey, haveVal, ok := r.Min()
				wantKey := 0
				wantVal := 0
				wok := false
				for k, v := range slice {
					if v != 0 && in(k, blo, bhi) {
						wantKey = k
						wantVal = v
						wok = true
						break
					}
				}
				if haveKey != wantKey || haveVal != wantVal || ok != wok {
					t.Errorf("N=%d, r=%s: Min() returned %d, %d, %t want %d, %d, %t",
						N, rdump(r), haveKey, haveVal, ok, wantKey, wantVal, wok)
				}
			}
		}
	})
}

func TestMaxRange(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			for blo, bhi := range bounds(N) {
				m := newMap()
				_, slice := permute(m, N)
				r := newMapSpan(m, blo, bhi)
				haveKey, haveVal, ok := r.Max()
				wantKey := 0
				wantVal := 0
				wok := false
				for k, v := range slice {
					k = len(slice) - k - 1
					if v != 0 && in(k, blo, bhi) {
						wantKey = k
						wantVal = slice[k]
						wok = true
						break
					}
				}
				if haveKey != wantKey || haveVal != wantVal || ok != wok {
					t.Errorf("N=%d, r=%s: Max() returned %d, %d, %t want %d, %d, %t",
						N, rdump(r), haveKey, haveVal, ok, wantKey, wantVal, wok)
				}
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

func TestKeys(t *testing.T) {
	t.Run("OMap", func(t *testing.T) {
		for N := range 11 {
			m := &_OMap[int, int]{}
			_, slice := permute(m, N)
			var have []int
			for k := range m.Keys() {
				have = append(have, k)
				if len(have) > N+5 {
					break
				}
			}
			want := nonzeroIndexes(slice)
			if !slices.Equal(have, want) {
				t.Errorf("N=%d: Keys() = %v, want %v", N, have, want)
			}
		}
	})
	t.Run("Map", func(t *testing.T) {
		for N := range 11 {
			m := NewMap[int, int](cmp.Compare)
			_, slice := permute(m, N)
			var have []int
			for k := range m.Keys() {
				have = append(have, k)
				if len(have) > N+5 {
					break
				}
			}
			want := nonzeroIndexes(slice)
			if !slices.Equal(have, want) {
				t.Errorf("N=%d: Keys() = %v, want %v", N, have, want)
			}
		}
	})
}

func TestValues(t *testing.T) {
	t.Run("OMap", func(t *testing.T) {
		for N := range 11 {
			m := &_OMap[int, int]{}
			_, slice := permute(m, N)
			var have []int
			for v := range m.Values() {
				have = append(have, v)
				if len(have) > N+5 {
					break
				}
			}
			var want []int
			for _, k := range nonzeroIndexes(slice) {
				want = append(want, slice[k])
			}
			if !slices.Equal(have, want) {
				t.Errorf("N=%d: Values() = %v, want %v", N, have, want)
			}
		}
	})
	t.Run("Map", func(t *testing.T) {
		for N := range 11 {
			m := NewMap[int, int](cmp.Compare)
			_, slice := permute(m, N)
			var have []int
			for v := range m.Values() {
				have = append(have, v)
				if len(have) > N+5 {
					break
				}
			}
			var want []int
			for _, k := range nonzeroIndexes(slice) {
				want = append(want, slice[k])
			}
			if !slices.Equal(have, want) {
				t.Errorf("N=%d: Values() = %v, want %v", N, have, want)
			}
		}
	})
}

func Test_backwardKeys(t *testing.T) {
	t.Run("OMap", func(t *testing.T) {
		for N := range 11 {
			m := &_OMap[int, int]{}
			_, slice := permute(m, N)
			var have []int
			for k := range m.backwardKeys() {
				have = append(have, k)
				if len(have) > N+5 {
					break
				}
			}
			want := nonzeroIndexes(slice)
			slices.Reverse(want)
			if !slices.Equal(have, want) {
				t.Errorf("N=%d: backwardKeys() = %v, want %v", N, have, want)
			}
		}
	})
	t.Run("Map", func(t *testing.T) {
		for N := range 11 {
			m := NewMap[int, int](cmp.Compare)
			_, slice := permute(m, N)
			var have []int
			for k := range m.backwardKeys() {
				have = append(have, k)
				if len(have) > N+5 {
					break
				}
			}
			want := nonzeroIndexes(slice)
			slices.Reverse(want)
			if !slices.Equal(have, want) {
				t.Errorf("N=%d: backwardKeys() = %v, want %v", N, have, want)
			}
		}
	})
}

func Test_backwardValues(t *testing.T) {
	t.Run("OMap", func(t *testing.T) {
		for N := range 11 {
			m := &_OMap[int, int]{}
			_, slice := permute(m, N)
			var have []int
			for v := range m.backwardValues() {
				have = append(have, v)
				if len(have) > N+5 {
					break
				}
			}
			want := nonzeroIndexes(slice)
			slices.Reverse(want)
			var wantVals []int
			for _, k := range want {
				wantVals = append(wantVals, slice[k])
			}
			if !slices.Equal(have, wantVals) {
				t.Errorf("N=%d: backwardValues() = %v, want %v", N, have, wantVals)
			}
		}
	})
	t.Run("Map", func(t *testing.T) {
		for N := range 11 {
			m := NewMap[int, int](cmp.Compare)
			_, slice := permute(m, N)
			var have []int
			for v := range m.backwardValues() {
				have = append(have, v)
				if len(have) > N+5 {
					break
				}
			}
			want := nonzeroIndexes(slice)
			slices.Reverse(want)
			var wantVals []int
			for _, k := range want {
				wantVals = append(wantVals, slice[k])
			}
			if !slices.Equal(have, wantVals) {
				t.Errorf("N=%d: backwardValues() = %v, want %v", N, have, wantVals)
			}
		}
	})
}

func TestAllRange(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		check := func(m Interface[int, int], slice []int, blo, bhi bound[int]) {
			var have []int
			r := newMapSpan(m, blo, bhi)
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
			for blo, bhi := range bounds(len(slice)) {
				check(m, slice, blo, bhi)
			}
		}
	})
}

func TestBackwardRange(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		check := func(m Interface[int, int], slice []int, blo, bhi bound[int]) {
			var have []int
			r := newMapSpan(m, blo, bhi)
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
				t.Errorf("Backward(%s) = %v, want %v", rdump(r), have, want)
			}
		}

		for N := range 11 {
			m := newMap()
			_, slice := permute(m, N)
			for blo, bhi := range bounds(len(slice)) {
				check(m, slice, blo, bhi)
			}
		}
	})
}

func TestKeysRange(t *testing.T) {
	t.Run("ORange", func(t *testing.T) {
		for N := range 11 {
			m := &_OMap[int, int]{}
			_, slice := permute(m, N)
			for blo, bhi := range bounds(len(slice)) {
				r := _OMapSpan[int, int]{m: m, _lo: blo, _hi: bhi}
				var have []int
				for k := range r.Keys() {
					have = append(have, k)
					if len(have) > len(slice)+5 {
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
					t.Errorf("N=%d, r=%s: Keys() = %v, want %v", N, rdump(r), have, want)
				}
			}
		}
	})
	t.Run("Range", func(t *testing.T) {
		for N := range 11 {
			m := NewMap[int, int](cmp.Compare)
			_, slice := permute(m, N)
			for blo, bhi := range bounds(len(slice)) {
				r := MapSpan[int, int]{m: m, _lo: blo, _hi: bhi}
				var have []int
				for k := range r.Keys() {
					have = append(have, k)
					if len(have) > len(slice)+5 {
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
					t.Errorf("N=%d, r=%s: Keys() = %v, want %v", N, rdump(r), have, want)
				}
			}
		}
	})
}

func TestValuesRange(t *testing.T) {
	t.Run("ORange", func(t *testing.T) {
		for N := range 11 {
			m := &_OMap[int, int]{}
			_, slice := permute(m, N)
			for blo, bhi := range bounds(len(slice)) {
				r := _OMapSpan[int, int]{m: m, _lo: blo, _hi: bhi}
				var have []int
				for v := range r.Values() {
					have = append(have, v)
					if len(have) > len(slice)+5 {
						break
					}
				}
				var want []int
				for k, v := range slice {
					if v != 0 && in(k, blo, bhi) {
						want = append(want, v)
					}
				}
				if !slices.Equal(have, want) {
					t.Errorf("N=%d, r=%s: Values() = %v, want %v", N, rdump(r), have, want)
				}
			}
		}
	})
	t.Run("Range", func(t *testing.T) {
		for N := range 11 {
			m := NewMap[int, int](cmp.Compare)
			_, slice := permute(m, N)
			for blo, bhi := range bounds(len(slice)) {
				r := MapSpan[int, int]{m: m, _lo: blo, _hi: bhi}
				var have []int
				for v := range r.Values() {
					have = append(have, v)
					if len(have) > len(slice)+5 {
						break
					}
				}
				var want []int
				for k, v := range slice {
					if v != 0 && in(k, blo, bhi) {
						want = append(want, v)
					}
				}
				if !slices.Equal(have, want) {
					t.Errorf("N=%d, r=%s: Values() = %v, want %v", N, rdump(r), have, want)
				}
			}
		}
	})
}

func Test_backwardKeysRange(t *testing.T) {
	t.Run("ORange", func(t *testing.T) {
		for N := range 11 {
			m := &_OMap[int, int]{}
			_, slice := permute(m, N)
			for blo, bhi := range bounds(len(slice)) {
				r := _OMapSpan[int, int]{m: m, _lo: blo, _hi: bhi}
				var have []int
				for k := range r.backwardKeys() {
					have = append(have, k)
					if len(have) > len(slice)+5 {
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
					t.Errorf("N=%d, r=%s: backwardKeys() = %v, want %v", N, rdump(r), have, want)
				}
			}
		}
	})
	t.Run("Range", func(t *testing.T) {
		for N := range 11 {
			m := NewMap[int, int](cmp.Compare)
			_, slice := permute(m, N)
			for blo, bhi := range bounds(len(slice)) {
				r := MapSpan[int, int]{m: m, _lo: blo, _hi: bhi}
				var have []int
				for k := range r.backwardKeys() {
					have = append(have, k)
					if len(have) > len(slice)+5 {
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
					t.Errorf("N=%d, r=%s: backwardKeys() = %v, want %v", N, rdump(r), have, want)
				}
			}
		}
	})
}

func Test_backwardValuesRange(t *testing.T) {
	t.Run("ORange", func(t *testing.T) {
		for N := range 11 {
			m := &_OMap[int, int]{}
			_, slice := permute(m, N)
			for blo, bhi := range bounds(len(slice)) {
				r := _OMapSpan[int, int]{m: m, _lo: blo, _hi: bhi}
				var have []int
				for v := range r.backwardValues() {
					have = append(have, v)
					if len(have) > len(slice)+5 {
						break
					}
				}
				var want []int
				for k, v := range slice {
					if v != 0 && in(k, blo, bhi) {
						want = append(want, v)
					}
				}
				slices.Reverse(want)
				if !slices.Equal(have, want) {
					t.Errorf("N=%d, r=%s: backwardValues() = %v, want %v", N, rdump(r), have, want)
				}
			}
		}
	})
	t.Run("Range", func(t *testing.T) {
		for N := range 11 {
			m := NewMap[int, int](cmp.Compare)
			_, slice := permute(m, N)
			for blo, bhi := range bounds(len(slice)) {
				r := MapSpan[int, int]{m: m, _lo: blo, _hi: bhi}
				var have []int
				for v := range r.backwardValues() {
					have = append(have, v)
					if len(have) > len(slice)+5 {
						break
					}
				}
				var want []int
				for k, v := range slice {
					if v != 0 && in(k, blo, bhi) {
						want = append(want, v)
					}
				}
				slices.Reverse(want)
				if !slices.Equal(have, want) {
					t.Errorf("N=%d, r=%s: backwardValues() = %v, want %v", N, rdump(r), have, want)
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
				if _, ok := m.Delete(x); ok {
					wantLen--
				}
				checkLen(m, wantLen)
				slice[x] = 0
				var have []int
				for k := range m.All() {
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

func TestClone(t *testing.T) {
	equal := func(i1, i2 Interface[int, int]) bool {
		if i1.Len() != i2.Len() {
			return false
		}
		next, stop := iter.Pull2(i2.All())
		defer stop()
		for k1, v1 := range i1.All() {
			k2, v2, ok := next()
			if !ok || k1 != k2 || v1 != v2 {
				return false
			}
		}
		return true
	}

	t.Run("Map", func(t *testing.T) {
		for N := range 11 {
			m := &_OMap[int, int]{}
			permute(m, N)
			if !equal(m, m.Clone()) {
				t.Errorf("N=%d: not equal", N)
			}
		}
	})
	t.Run("MapFunc", func(t *testing.T) {
		for N := range 11 {
			m := NewMap[int, int](func(i1, i2 int) int { return cmp.Compare(i1, i2) })
			permute(m, N)
			if !equal(m, m.Clone()) {
				t.Errorf("N=%d: not equal", N)
			}
		}
	})
}

func TestDeleteRange(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		check := func(N int, blo, bhi bound[int], clearReverse bool) {
			t.Helper()
			m := newMap()
			r := newMapSpan(m, blo, bhi)
			_, slice := permute(m, N)
			if clearReverse {
				newMapSpan(m, bhi, blo).Clear()
			}
			newMapSpan(m, blo, bhi).Clear()
			var have []int
			for k := range m.All() {
				have = append(have, k)
			}
			want := keep(slice, func(k int) bool { return !in(k, blo, bhi) })
			if !slices.Equal(have, want) {
				t.Errorf("N=%d, after Clear(%s), All() = %v, want %v",
					N, rdump(r), have, want)
			}
			if g, w := m.Len(), len(have); g != w {
				t.Errorf("m.Len() = %d, want %d", g, w)
			}
		}

		for N := range 11 {
			for blo, bhi := range bounds(2*N + 1) {
				check(N, blo, bhi, blo.present && bhi.present && blo.key < bhi.key)
			}
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
					for k := range m.All() {
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
					for k := range m.Backward() {
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
		newMapSpan(m, including(deleteLo), including(deleteHi)).Clear()
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

func TestNth(t *testing.T) {
	test(t, func(t *testing.T, newMap func() Interface[int, int]) {
		for N := range 11 {
			m := newMap()
			_, slice := permute(m, N)
			var haveKeys, haveVals []int
			for i := range N {
				k, v := m.Nth(i)
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

func TestIndex(t *testing.T) {
	t.Run("OMap", func(t *testing.T) {
		var m _OMap[int, int]
		// Empty map
		if got := m.Index(1); got != -1 {
			t.Errorf("empty map: got %d, want -1", got)
		}

		// Insert keys 2, 4, 6, 8, 10
		for i := 1; i <= 5; i++ {
			m.Set(2*i, i)
		}

		// Test existing keys
		for i := range 5 {
			key := 2 * (i + 1) // keys 2, 4, 6, 8, 10
			if got := m.Index(key); got != i {
				t.Errorf("Index(%d): got %d, want %d", key, got, i)
			}
		}

		// Test non-existing keys
		for _, key := range []int{1, 3, 5, 100} {
			if got := m.Index(key); got != -1 {
				t.Errorf("Index(%d): got %d, want -1", key, got)
			}
		}
	})

	t.Run("Map", func(t *testing.T) {
		m := NewMap[int, int](cmp.Compare)
		// Empty map
		if got := m.Index(1); got != -1 {
			t.Errorf("empty map: got %d, want -1", got)
		}

		// Insert keys 2, 4, 6, 8, 10
		for i := 1; i <= 5; i++ {
			m.Set(2*i, i)
		}

		// Test existing keys
		for i := range 5 {
			key := 2 * (i + 1)
			if got := m.Index(key); got != i {
				t.Errorf("Index(%d): got %d, want %d", key, got, i)
			}
		}

		// Test non-existing keys
		for _, key := range []int{1, 3, 5, 100} {
			if got := m.Index(key); got != -1 {
				t.Errorf("Index(%d): got %d, want -1", key, got)
			}
		}
	})

	t.Run("ORange", func(t *testing.T) {
		var m _OMap[int, int]
		// Insert keys 2, 4, 6, 8, 10
		for i := 1; i <= 5; i++ {
			m.Set(2*i, i)
		}

		// Range [4, 8] contains 4, 6, 8 at indices 0, 1, 2
		r := m.From(4).To(8)
		for i, key := range []int{4, 6, 8} {
			if got := r.Index(key); got != i {
				t.Errorf("Range.Index(%d): got %d, want %d", key, got, i)
			}
		}

		// Keys in map but outside range
		for _, key := range []int{2, 10} {
			if got := r.Index(key); got != -1 {
				t.Errorf("Range.Index(%d): got %d, want -1", key, got)
			}
		}

		// Keys not in map
		for _, key := range []int{1, 5, 100} {
			if got := r.Index(key); got != -1 {
				t.Errorf("Range.Index(%d): got %d, want -1", key, got)
			}
		}
	})

	t.Run("Range", func(t *testing.T) {
		m := NewMap[int, int](cmp.Compare)
		// Insert keys 2, 4, 6, 8, 10
		for i := 1; i <= 5; i++ {
			m.Set(2*i, i)
		}

		// Range [4, 8] contains 4, 6, 8 at indices 0, 1, 2
		r := m.From(4).To(8)
		for i, key := range []int{4, 6, 8} {
			if got := r.Index(key); got != i {
				t.Errorf("Range.Index(%d): got %d, want %d", key, got, i)
			}
		}

		// Keys in map but outside range
		for _, key := range []int{2, 10} {
			if got := r.Index(key); got != -1 {
				t.Errorf("Range.Index(%d): got %d, want -1", key, got)
			}
		}

		// Keys not in map
		for _, key := range []int{1, 5, 100} {
			if got := r.Index(key); got != -1 {
				t.Errorf("Range.Index(%d): got %d, want -1", key, got)
			}
		}
	})
}

func TestRangeLen(t *testing.T) {
	t.Run("ORange", func(t *testing.T) {
		var m _OMap[int, int]
		// Empty range on empty map
		if got := m.From(1).To(10).Len(); got != 0 {
			t.Errorf("empty map: got %d, want 0", got)
		}

		// Insert keys 2, 4, 6, 8, 10
		for i := 1; i <= 5; i++ {
			m.Set(2*i, i)
		}

		// Full map
		if got := m.From(0).To(100).Len(); got != 5 {
			t.Errorf("full range: got %d, want 5", got)
		}

		// Range [4, 8] contains 4, 6, 8
		if got := m.From(4).To(8).Len(); got != 3 {
			t.Errorf("From(4).To(8): got %d, want 3", got)
		}

		// Range (4, 8) contains only 6
		if got := m.Above(4).Below(8).Len(); got != 1 {
			t.Errorf("Above(4).Below(8): got %d, want 1", got)
		}

		// Empty range
		if got := m.From(100).To(200).Len(); got != 0 {
			t.Errorf("empty range: got %d, want 0", got)
		}
	})

	t.Run("Range", func(t *testing.T) {
		m := NewMap[int, int](cmp.Compare)
		// Empty range on empty map
		if got := m.From(1).To(10).Len(); got != 0 {
			t.Errorf("empty map: got %d, want 0", got)
		}

		// Insert keys 2, 4, 6, 8, 10
		for i := 1; i <= 5; i++ {
			m.Set(2*i, i)
		}

		// Full map
		if got := m.From(0).To(100).Len(); got != 5 {
			t.Errorf("full range: got %d, want 5", got)
		}

		// Range [4, 8] contains 4, 6, 8
		if got := m.From(4).To(8).Len(); got != 3 {
			t.Errorf("From(4).To(8): got %d, want 3", got)
		}

		// Range (4, 8) contains only 6
		if got := m.Above(4).Below(8).Len(); got != 1 {
			t.Errorf("Above(4).Below(8): got %d, want 1", got)
		}

		// Empty range
		if got := m.From(100).To(200).Len(); got != 0 {
			t.Errorf("empty range: got %d, want 0", got)
		}
	})
}

func TestRangeNth(t *testing.T) {
	t.Run("ORange", func(t *testing.T) {
		var m _OMap[int, int]
		// Insert keys 2, 4, 6, 8, 10 with values 1, 2, 3, 4, 5
		for i := 1; i <= 5; i++ {
			m.Set(2*i, i)
		}

		// Range [4, 8] contains 4, 6, 8
		r := m.From(4).To(8)
		for i, wantKey := range []int{4, 6, 8} {
			k, v := r.Nth(i)
			if k != wantKey {
				t.Errorf("Nth(%d) key: got %d, want %d", i, k, wantKey)
			}
			if v != wantKey/2 {
				t.Errorf("Nth(%d) value: got %d, want %d", i, v, wantKey/2)
			}
		}
	})

	t.Run("Range", func(t *testing.T) {
		m := NewMap[int, int](cmp.Compare)
		// Insert keys 2, 4, 6, 8, 10 with values 1, 2, 3, 4, 5
		for i := 1; i <= 5; i++ {
			m.Set(2*i, i)
		}

		// Range [4, 8] contains 4, 6, 8
		r := m.From(4).To(8)
		for i, wantKey := range []int{4, 6, 8} {
			k, v := r.Nth(i)
			if k != wantKey {
				t.Errorf("Nth(%d) key: got %d, want %d", i, k, wantKey)
			}
			if v != wantKey/2 {
				t.Errorf("Nth(%d) value: got %d, want %d", i, v, wantKey/2)
			}
		}
	})
}

func TestRangeClone(t *testing.T) {
	t.Run("ORange", func(t *testing.T) {
		var m _OMap[int, int]
		// Insert keys 2, 4, 6, 8, 10 with values 1, 2, 3, 4, 5
		for i := 1; i <= 5; i++ {
			m.Set(2*i, i)
		}

		// Clone range [4, 8]
		clone := m.From(4).To(8).Clone()
		if clone.Len() != 3 {
			t.Errorf("Len: got %d, want 3", clone.Len())
		}
		for i, key := range []int{4, 6, 8} {
			k, v := clone.Nth(i)
			if k != key || v != key/2 {
				t.Errorf("Nth(%d): got (%d, %d), want (%d, %d)", i, k, v, key, key/2)
			}
		}

		// Verify clone is independent
		clone.Set(5, 99)
		if m.Len() != 5 {
			t.Errorf("original modified: Len = %d, want 5", m.Len())
		}
	})

	t.Run("Range", func(t *testing.T) {
		m := NewMap[int, int](cmp.Compare)
		// Insert keys 2, 4, 6, 8, 10 with values 1, 2, 3, 4, 5
		for i := 1; i <= 5; i++ {
			m.Set(2*i, i)
		}

		// Clone range [4, 8]
		clone := m.From(4).To(8).Clone()
		if clone.Len() != 3 {
			t.Errorf("Len: got %d, want 3", clone.Len())
		}
		for i, key := range []int{4, 6, 8} {
			k, v := clone.Nth(i)
			if k != key || v != key/2 {
				t.Errorf("Nth(%d): got (%d, %d), want (%d, %d)", i, k, v, key, key/2)
			}
		}

		// Verify clone is independent
		clone.Set(5, 99)
		if m.Len() != 5 {
			t.Errorf("original modified: Len = %d, want 5", m.Len())
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

func TestRangeCreation(t *testing.T) {
	t.Run("Map", func(t *testing.T) {
		m := &_OMap[int, int]{}

		for _, tc := range []struct {
			r    _OMapSpan[int, int]
			want string
		}{
			{m.From(2), "[2, ∞)"},
			{m.Above(2), "(2, ∞)"},
			{m.To(2), "(-∞, 2]"},
			{m.Below(2), "(-∞, 2)"},
			{m.From(2).To(5), "[2, 5]"},
			{m.From(2).Below(5), "[2, 5)"},
			{m.Above(2).To(5), "(2, 5]"},
			{m.Above(2).Below(5), "(2, 5)"},
		} {
			got := rdump(tc.r)
			if got != tc.want {
				t.Errorf("got %s, want %s", got, tc.want)
			}
		}
	})

	t.Run("MapFunc", func(t *testing.T) {
		m := NewMap[int, int](nil)
		for _, tc := range []struct {
			r    MapSpan[int, int]
			want string
		}{
			{m.From(2), "[2, ∞)"},
			{m.Above(2), "(2, ∞)"},
			{m.To(2), "(-∞, 2]"},
			{m.Below(2), "(-∞, 2)"},
			{m.From(2).To(5), "[2, 5]"},
			{m.From(2).Below(5), "[2, 5)"},
			{m.Above(2).To(5), "(2, 5]"},
			{m.Above(2).Below(5), "(2, 5)"},
		} {
			got := rdump(tc.r)
			if got != tc.want {
				t.Errorf("got %s, want %s", got, tc.want)
			}
		}
	})
}

type iRange[K, V any] interface {
	Clear()
	All() iter.Seq2[K, V]
	Backward() iter.Seq2[K, V]
	Min() (K, V, bool)
	Max() (K, V, bool)
}

func rdump[K, V any](ir iRange[K, V]) string {
	r := ir.(_range[K, V])
	var b strings.Builder
	if !r.lo().present {
		b.WriteString("(-∞")
	} else {
		if r.lo().inclusive {
			b.WriteByte('[')
		} else {
			b.WriteByte('(')
		}
		fmt.Fprintf(&b, "%v", r.lo().key)
	}
	b.WriteString(", ")
	if !r.hi().present {
		b.WriteString("∞)")
	} else {
		fmt.Fprintf(&b, "%v", r.hi().key)
		if r.hi().inclusive {
			b.WriteByte(']')
		} else {
			b.WriteByte(')')
		}
	}
	return b.String()
}

func newMapSpan[K cmp.Ordered, V any](m Interface[K, V], lo, hi bound[K]) iRange[K, V] {
	switch m := m.(type) {
	case *_OMap[K, V]:
		return _OMapSpan[K, V]{m: m, _lo: lo, _hi: hi}
	case *Map[K, V]:
		return MapSpan[K, V]{m: m, _lo: lo, _hi: hi}
	default:
		panic("bad map type")
	}
}

func inf() bound[int] { return bound[int]{} }

// bounds returns a sequence of all pairs of bound[int] for numbers in [0, n).
func bounds(n int) iter.Seq2[bound[int], bound[int]] {
	return func(yield func(_, _ bound[int]) bool) {
		for hi := range n {
			for _, bhi := range []bound[int]{including(hi), excluding(hi), inf()} {
				for lo := range hi + 1 {
					for _, blo := range []bound[int]{including(lo), excluding(lo), inf()} {
						if blo == inf() && bhi == inf() {
							continue
						}
						if !yield(blo, bhi) {
							return
						}
					}
				}
			}
		}
		// Produce an interval past the end. We already generate one before
		// the beginning, (-∞, 0).
		if !yield(excluding(n), inf()) {
			return
		}
		// Yield the infinite interval even if n == 0.
		yield(inf(), inf())
	}
}

func TestBounds(t *testing.T) {
	got := map[string]bool{}
	for blo, bhi := range bounds(2) {
		got[rdump(newMapSpan(&_OMap[int, int]{}, blo, bhi))] = true
	}
	wants := []string{
		"(0, 0)",
		"(0, 1)",
		"(0, ∞)",
		"[0, 0)",
		"[0, 1)",
		"[0, ∞)",
		"(0, 0]",
		"(0, 1]",
		"[0, 0]",
		"[0, 1]",

		"(1, 1)",
		"(1, ∞)",
		"[1, 1)",
		"[1, ∞)",
		"(1, 1]",
		"[1, 1]",

		"(-∞, 0)",
		"(-∞, 0]",
		"(-∞, 1)",
		"(-∞, 1]",

		"(2, ∞)",
		"(-∞, ∞)",
	}

	want := map[string]bool{}
	for _, w := range wants {
		want[w] = true
	}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("got %v, want %v", got, want)
	}
}

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

func TestRdump(t *testing.T) {
	m := newMap(nil)
	for _, test := range []struct {
		r    iRange[int, int]
		want string
	}{
		{newMapSpan(m, inf(), inf()), "(-∞, ∞)"},
		{newMapSpan(m, including(1), inf()), "[1, ∞)"},
		{newMapSpan(m, inf(), excluding(3)), "(-∞, 3)"},
		{newMapSpan(m, including(1), including(3)), "[1, 3]"},
		{newMapSpan(m, including(1), excluding(3)), "[1, 3)"},
		{newMapSpan(m, excluding(1), including(3)), "(1, 3]"},
		{newMapSpan(m, excluding(1), excluding(3)), "(1, 3)"},
	} {
		got := rdump[int, int](test.r)
		if got != test.want {
			t.Errorf("%v: got %q, want %q", test.r, got, test.want)
		}
	}
}

func TestRangeBounds(t *testing.T) {
	m := NewMap[int, int](cmp.Compare[int])
	for _, test := range []struct {
		name string
		got  MapSpan[int, int]
		want string
	}{
		{
			"To1",
			MapSpan[int, int]{m, inf(), inf()}.To(10),
			"(-∞, 10]",
		},
		{
			"To2",
			MapSpan[int, int]{m, inf(), including(10)}.To(10),
			"(-∞, 10]",
		},
		{
			"To3",
			MapSpan[int, int]{m, inf(), excluding(10)}.To(10),
			"(-∞, 10)",
		},
		{
			"To4",
			MapSpan[int, int]{m, inf(), including(9)}.To(10),
			"(-∞, 9]",
		},
		{
			"Below1",
			MapSpan[int, int]{m, inf(), inf()}.Below(10),
			"(-∞, 10)",
		},
		{
			"Below2",
			MapSpan[int, int]{m, inf(), including(10)}.Below(10),
			"(-∞, 10)",
		},
		{
			"Below3",
			MapSpan[int, int]{m, inf(), excluding(10)}.Below(10),
			"(-∞, 10)",
		},
		{
			"Below4",
			MapSpan[int, int]{m, inf(), including(9)}.Below(10),
			"(-∞, 9]",
		},
		{
			"From1",
			MapSpan[int, int]{m, inf(), inf()}.From(10),
			"[10, ∞)",
		},
		{
			"From2",
			MapSpan[int, int]{m, including(10), inf()}.From(10),
			"[10, ∞)",
		},
		{
			"From3",
			MapSpan[int, int]{m, excluding(10), inf()}.From(10),
			"(10, ∞)",
		},
		{
			"From4",
			MapSpan[int, int]{m, including(11), inf()}.From(10),
			"[11, ∞)",
		},
		{
			"Above1",
			MapSpan[int, int]{m, inf(), inf()}.Above(10),
			"(10, ∞)",
		},
		{
			"Above2",
			MapSpan[int, int]{m, including(10), inf()}.Above(10),
			"(10, ∞)",
		},
		{
			"Above3",
			MapSpan[int, int]{m, excluding(10), inf()}.Above(10),
			"(10, ∞)",
		},
		{
			"Above4",
			MapSpan[int, int]{m, including(11), inf()}.Above(10),
			"[11, ∞)",
		},
	} {
		t.Run(test.name, func(t *testing.T) {
			got := rdump[int, int](test.got)
			if got != test.want {
				t.Errorf("got %s, want %s", got, test.want)
			}
		})
	}
}

func TestString(t *testing.T) {
	// Map and _OMap
	for _, m := range []Interface[int, string]{
		NewMap[int, string](cmp.Compare),
		new(_OMap[int, string]),
	} {
		if got, want := m.String(), "{}"; got != want {
			t.Errorf("%T.String() = %q, want %q", m, got, want)
		}
		m.Set(1, "one")
		m.Set(2, "two")
		if got, want := m.String(), "{1: one, 2: two}"; got != want {
			t.Errorf("%T.String() = %q, want %q", m, got, want)
		}
	}

	// MapSpan and _OMapSpan
	mm := NewMap[int, string](cmp.Compare)
	mm.Set(1, "one")
	mm.Set(2, "two")
	mm.Set(3, "three")

	om := new(_OMap[int, string])
	om.Set(1, "one")
	om.Set(2, "two")
	om.Set(3, "three")

	for _, test := range []struct {
		name string
		got  string
		want string
	}{
		{"MapSpanEmpty", mm.Above(3).String(), "{}"},
		{"MapSpanOne", mm.From(2).To(2).String(), "{2: two}"},
		{"MapSpanFull", mm.From(-1).To(10).String(), "{1: one, 2: two, 3: three}"},
		{"_OMapSpanEmpty", om.Above(3).String(), "{}"},
		{"_OMapSpanOne", om.From(2).To(2).String(), "{2: two}"},
		{"_OMapSpanFull", om.From(-1).To(10).String(), "{1: one, 2: two, 3: three}"},
	} {
		if test.got != test.want {
			t.Errorf("%s = %q, want %q", test.name, test.got, test.want)
		}
	}
}

var _ AbstractMap[int, int, *Map[int, int]] = NewMap[int, int](cmp.Compare)

// copied temporarily from https://go-review.git.corp.google.com/c/go/+/761460/1/src/container/container_test.go

type AbstractCollection[E any, C AbstractCollection[E, C]] interface {
	Clear()
	Clone() C
	Contains(e E) bool
	ContainsAll(seq iter.Seq[E]) bool
	Len() int
	String() string
}

type AbstractMap[K, V any, M AbstractMap[K, V, M]] interface {
	AbstractCollection[K, M]

	All() iter.Seq2[K, V]
	At(key K) V
	Delete(key K) (V, bool)
	DeleteAll(keys iter.Seq[K]) bool
	Get(key K) (V, bool)
	Keys() iter.Seq[K]
	Set(K, V) (V, bool)
	SetAll(iter.Seq2[K, V]) bool
	Values() iter.Seq[V]
}
