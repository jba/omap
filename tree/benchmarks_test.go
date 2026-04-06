// Copyright 2024 The Go Authors. All rights reserved.

// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// These benchmarks are based on the ones in github.com/google/btree.

package tree

import (
	"math/rand/v2"
	"sort"
	"testing"
)

const benchmarkTreeSize = 10_000

func BenchmarkInsert(b *testing.B) {
	b.StopTimer()
	insertP := rand.Perm(benchmarkTreeSize)
	b.StartTimer()
	i := 0
	for i < b.N {
		var m _OMap[int, int]
		for _, item := range insertP {
			m.Set(item, item)
			i++
			if i >= b.N {
				return
			}
		}
	}
}

func randMap(size int) (*_OMap[int, int], []int) {
	insertP := rand.Perm(size)
	var m _OMap[int, int]
	for _, item := range insertP {
		m.Set(item, item)
	}
	return &m, insertP
}

func newMap(els []int) *_OMap[int, int] {
	var m _OMap[int, int]
	for _, item := range els {
		m.Set(item, item)
	}
	return &m
}

// iterator setup
func BenchmarkSeek(b *testing.B) {
	b.StopTimer()
	size := 100_000
	m, _ := randMap(size)
	b.StartTimer()

	for i := range b.N {
		for range m.From(i % size).All() {
			break
		}
	}
}

func BenchmarkDeleteInsert(b *testing.B) {
	b.StopTimer()
	m, insertP := randMap(benchmarkTreeSize)
	b.StartTimer()
	for i := range b.N {
		m.Delete(insertP[i%benchmarkTreeSize])
		m.Set(insertP[i%benchmarkTreeSize], i)
	}
}

func BenchmarkDelete(b *testing.B) {
	b.StopTimer()
	insertP := rand.Perm(benchmarkTreeSize)
	removeP := rand.Perm(benchmarkTreeSize)
	b.StartTimer()
	i := 0
	for i < b.N {
		b.StopTimer()
		m := newMap(insertP)
		b.StartTimer()
		for _, item := range removeP {
			m.Delete(item)
			i++
			if i >= b.N {
				return
			}
		}
	}
}

func BenchmarkGet(b *testing.B) {
	b.StopTimer()
	insertP := rand.Perm(benchmarkTreeSize)
	removeP := rand.Perm(benchmarkTreeSize)
	b.StartTimer()
	i := 0
	for i < b.N {
		b.StopTimer()
		m := newMap(insertP)
		b.StartTimer()
		for _, item := range removeP {
			m.Get(item)
			i++
			if i >= b.N {
				return
			}
		}
	}
}

func BenchmarkGetSame(b *testing.B) {
	m := newMap(rand.Perm(benchmarkTreeSize))
	seq := rand.Perm(benchmarkTreeSize)
	for b.Loop() {
		for _, item := range seq {
			m.Get(item)
		}
	}
}

func BenchmarkAscend(b *testing.B) {
	arr := rand.Perm(benchmarkTreeSize)
	m := newMap(arr)
	sort.Ints(arr)
	b.ResetTimer()
	for range b.N {
		j := 0
		for k := range m.All() {
			if k != arr[j] {
				b.Fatalf("mismatch: expected: %v, got %v", arr[j], k)
			}
			j++
		}
	}
}
