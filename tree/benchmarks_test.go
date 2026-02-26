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
		var m OrderedMap[int, int]
		for _, item := range insertP {
			m.Insert(item, item)
			i++
			if i >= b.N {
				return
			}
		}
	}
}

func randMap(size int) (*OrderedMap[int, int], []int) {
	insertP := rand.Perm(size)
	var m OrderedMap[int, int]
	for _, item := range insertP {
		m.Insert(item, item)
	}
	return &m, insertP
}

func newMap(els []int) *OrderedMap[int, int] {
	var m OrderedMap[int, int]
	for _, item := range els {
		m.Insert(item, item)
	}
	return &m
}

// iterator setup
func BenchmarkSeek(b *testing.B) {
	b.StopTimer()
	size := 100_000
	m, _ := randMap(size)
	b.StartTimer()

	for i := 0; i < b.N; i++ {
		for range m.From(i % size).All() {
			break
		}
	}
}

func BenchmarkDeleteInsert(b *testing.B) {
	b.StopTimer()
	m, insertP := randMap(benchmarkTreeSize)
	b.StartTimer()
	for i := 0; i < b.N; i++ {
		m.Delete(insertP[i%benchmarkTreeSize])
		m.Insert(insertP[i%benchmarkTreeSize], i)
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
	for i := 0; i < b.N; i++ {
		j := 0
		for k := range m.All() {
			if k != arr[j] {
				b.Fatalf("mismatch: expected: %v, got %v", arr[j], k)
			}
			j++
		}
	}
}
