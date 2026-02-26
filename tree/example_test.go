// Copyright 2024 The Go Authors. All rights reserved.
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package tree_test

import (
	"fmt"

	"github.com/jba/omap/tree"
)

func ExampleMap_All() {
	m := &tree.OrderedMap[int, string]{}
	m.Insert(1, "one")
	m.Insert(2, "two")
	m.Insert(3, "three")

	for k, v := range m.All() {
		fmt.Println(k, v)
	}

	// Output:
	// 1 one
	// 2 two
	// 3 three
}

func ExampleMap_From() {
	m := &tree.OrderedMap[int, string]{}
	m.Insert(1, "one")
	m.Insert(2, "two")
	m.Insert(3, "three")

	for k, v := range m.From(2).All() {
		fmt.Println(k, v)
	}

	// Output:
	// 2 two
	// 3 three
}

func ExampleMap_Below() {
	m := &tree.OrderedMap[int, string]{}
	m.Insert(1, "one")
	m.Insert(2, "two")
	m.Insert(3, "three")

	for k, v := range m.Above(1).Below(3).All() {
		fmt.Println(k, v)
	}

	// Output:
	// 2 two
}
