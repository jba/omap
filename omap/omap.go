// XXXXXX
// TODO: support Len with a root counter

// Copyright 2024 The Go Authors. All rights reserved.

// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package omap implements in-memory ordered maps.
// [Map][K, V] is suitable for ordered types K,
// while [MapFunc][K, V] supports arbitrary keys and comparison functions.
package omap

// The implementation is a treap. See:
// https://en.wikipedia.org/wiki/Treap
// https://faculty.washington.edu/aragon/pubs/rst89.pdf

import (
	"cmp"
	"fmt"
	"strings"
	// "github.com/jba/omap/rng"
	"iter"
	"math/rand/v2"
)

// A Map is a map[K]V ordered according to K's standard Go ordering.
// The zero value of a Map is an empty Map ready to use.
type Map[K cmp.Ordered, V any] struct {
	_root *node[K, V]
}

// A MapFunc is a map[K]V ordered according to an arbitrary comparison function.
// The zero value of a MapFunc is not meaningful since it has no comparison function.
// Use [NewMapFunc] to create a [MapFunc].
// A nil *MapFunc, like a nil Go map, can be read but not written and contains no entries.
type MapFunc[K, V any] struct {
	_root *node[K, V]
	cmp   func(K, K) int
}

// A node is a node in the treap.
type node[K any, V any] struct {
	parent *node[K, V]
	left   *node[K, V]
	right  *node[K, V]
	key    K
	val    V
	pri    uint64
}

// NewMapFunc returns a new MapFunc[K, V] ordered according to cmp.
func NewMapFunc[K, V any](cmp func(K, K) int) *MapFunc[K, V] {
	return &MapFunc[K, V]{cmp: cmp}
}

// omap is the interface implemented by both Map[K, V] and MapFunc[K, V]
// that enables a common implementation of the map operations.
type omap[K, V any] interface {
	// root returns &m._root; the caller can read or write *m.root().
	root() **node[K, V]

	// find reports where a node with the key would be: at *pos.
	// If *pos != nil, then key is present in the tree;
	// otherwise *pos is where a new node with the key should be attached.
	//
	// If parent != nil, then pos is either &parent.left or &parent.right
	// depending on how parent.key compares with key.
	// If parent == nil, then pos is m.root().
	find(key K) (pos **node[K, V], parent *node[K, V])

	// TODO: remove by rewriting deleteRange.
	get(K) (V, bool)
	set(key K, val V)

	clear()
}

func (m *Map[K, V]) root() **node[K, V]     { return &m._root }
func (m *MapFunc[K, V]) root() **node[K, V] { return &m._root }

func (m *Map[K, V]) clear()     { m.Clear() }
func (m *MapFunc[K, V]) clear() { m.Clear() }

func (m *Map[K, V]) get(k K) (V, bool)     { return m.Get(k) }
func (m *MapFunc[K, V]) get(k K) (V, bool) { return m.Get(k) }

func (m *Map[K, V]) set(k K, v V)     { m.Set(k, v) }
func (m *MapFunc[K, V]) set(k K, v V) { m.Set(k, v) }

// find looks up the key k in the map.
// It returns the parent of k as well as the position where k would be attached.
// *pos is non-nil if k is present, nil if k is missing.
// parent is nil if there are no nodes in the map, or if there is only one node and it's k.
func (m *Map[K, V]) find(k K) (pos **node[K, V], parent *node[K, V]) {
	pos = &m._root
	for x := *pos; x != nil; x = *pos {
		if x.key == k {
			break
		}
		parent = x
		if x.key > k {
			pos = &x.left
		} else {
			pos = &x.right
		}
	}
	return pos, parent
}

// find is the same as for Map[K, V] but using m.cmp.
func (m *MapFunc[K, V]) find(k K) (pos **node[K, V], parent *node[K, V]) {
	pos = &m._root
	for x := *pos; x != nil; x = *pos {
		cmp := m.cmp(x.key, k)
		if cmp == 0 {
			break
		}
		parent = x
		if cmp > 0 {
			pos = &x.left
		} else {
			pos = &x.right
		}
	}
	return pos, parent
}

// Get returns the value of m[key] and reports whether it exists.
func (m *Map[K, V]) Get(key K) (V, bool) {
	return get(m, key)
}

// Get returns the value of m[key] and reports whether it exists.
func (m *MapFunc[K, V]) Get(key K) (V, bool) {
	return get(m, key)
}

func get[K, V any](m omap[K, V], key K) (V, bool) {
	pos, _ := m.find(key)
	if x := *pos; x != nil {
		return x.val, true
	}
	var zero V
	return zero, false
}

// Set sets m[key] = val.
// If the entry was present, Set returns the former value and false.
// Otherwise it returns the zero value and true.
func (m *Map[K, V]) Set(key K, val V) (old V, added bool) {
	return set(m, key, val)
}

// Set sets m[key] = val.
// If the entry was present, Set returns the former value and false.
// Otherwise it returns the zero value and true.
func (m *MapFunc[K, V]) Set(key K, val V) (old V, added bool) {
	return set(m, key, val)
}

func set[K, V any](m omap[K, V], key K, val V) (V, bool) {
	pos, parent := m.find(key)
	if x := *pos; x != nil {
		old := x.val
		x.val = val
		return old, false
	}
	x := &node[K, V]{key: key, val: val, pri: rand.Uint64() | 1, parent: parent}
	*pos = x
	rotateUp(m, x)
	var z V
	return z, true
}

// rotateUp rotates x upward in the tree to correct any priority inversions.
func rotateUp[K, V any](m omap[K, V], x *node[K, V]) {
	// Rotate up into tree according to priority.
	for x.parent != nil && x.parent.pri > x.pri {
		if x.parent.left == x {
			rotateRight(m, x.parent)
		} else {
			rotateLeft(m, x.parent)
		}
	}
}

// Delete deletes m[key] if it exists.
func (m *Map[K, V]) Delete(key K) {
	_delete(m, key)
}

// Delete deletes m[key] if it exists.
func (m *MapFunc[K, V]) Delete(key K) {
	_delete(m, key)
}

func _delete[K, V any](m omap[K, V], key K) {
	pos, _ := m.find(key)
	x := *pos
	if x == nil {
		return
	}

	// Rotate x down to be leaf of tree for removal, respecting priorities.
	for x.right != nil || x.left != nil {
		if x.right == nil || x.left != nil && x.left.pri < x.right.pri {
			rotateRight(m, x)
		} else {
			rotateLeft(m, x)
		}
	}

	// Remove x, now a leaf.
	switch p := x.parent; {
	case p == nil:
		*m.root() = nil
	case p.left == x:
		p.left = nil
	default:
		p.right = nil
	}
	x.pri = 0 // mark deleted
}

// Min returns the minimum key in m and true.
// If m is empty, the second return value is false.
func (m *Map[K, V]) Min() (K, bool) {
	return _min(m)
}

// Min returns the minimum key in m and true.
// If m is empty, the second return value is false.
func (m *MapFunc[K, v]) Min() (K, bool) {
	return _min(m)
}

func _min[K, V any](m omap[K, V]) (K, bool) {
	x := *m.root()
	if x == nil {
		var z K
		return z, false
	}
	return x.minNode().key, true
}

// minNode returns the node in x's subtree with the smallest key.
// x must not be nil.
func (x *node[K, V]) minNode() *node[K, V] {
	for x.left != nil {
		x = x.left
	}
	return x
}

// Max returns the Maximum key in m and true.
// If m is empty, the second return value is false.
func (m *Map[K, V]) Max() (K, bool) {
	return _max(m)
}

// Max returns the Maximum key in m and true.
// If m is empty, the second return value is false.
func (m *MapFunc[K, v]) Max() (K, bool) {
	return _max(m)
}

func _max[K, V any](m omap[K, V]) (K, bool) {
	x := *m.root()
	if x == nil {
		var z K
		return z, false
	}
	return x.maxNode().key, true
}

// maxNode returns the node in x's subtree with the smallest key.
// x must not be nil.
func (x *node[K, V]) maxNode() *node[K, V] {
	for x.right != nil {
		x = x.right
	}
	return x
}

func deleteRange[K, V any](m omap[K, V], lo, hi bound[K]) {
	// TODO: rewrite to avoid reinsertions.
	switch {
	case !lo.present && !hi.present:
		m.clear()
	case lo.present && hi.present:
		loVal, loPresent := m.get(lo.key)
		hiVal, hiPresent := m.get(hi.key)
		deleteBetweenInclusive(m, lo.key, hi.key)
		if !lo.inclusive && loPresent {
			m.set(lo.key, loVal)
		}
		if !hi.inclusive && hiPresent {
			m.set(hi.key, hiVal)
		}
	case lo.present:
		deleteAbove(m, lo)
	case hi.present:
		deleteBelow(m, hi)
	default:
		panic("unreachable")
	}
}

// Called deleteRange in rsc.io/omap.
func deleteBetweenInclusive[K, V any](m omap[K, V], lo, hi K) {
	after := splitExclusive(m, hi)
	middle := splitExclusive(m, lo)
	markDeleted(middle)
	if after != nil {
		// Add after to m.
		// Both lo and all of after's keys are greater than any key in m.
		pos, parent := m.find(lo)
		assert(*pos == nil)
		*pos = after
		after.parent = parent
		// after is now in the right place by key, but perhaps not by priority.
		rotateUp(m, after)
	}
}

func deleteAbove[K, V any](m omap[K, V], lo bound[K]) {
	assert(lo.present)
	val, ok := m.get(lo.key)
	after := splitExclusive(m, lo.key)
	markDeleted(after)
	if !lo.inclusive && ok {
		m.set(lo.key, val)
	}
}

func deleteBelow[K, V any](m omap[K, V], hi bound[K]) {
	assert(hi.present)
	val, ok := m.get(hi.key)
	after := splitExclusive(m, hi.key)
	// Keep after, discard m.
	markDeleted(*m.root())
	*m.root() = after
	if after != nil {
		after.parent = nil
	}
	if !hi.inclusive && ok {
		m.set(hi.key, val)
	}
}

// splitExclusive splits m into two subtrees.
// The returned node contains all keys > key.
// m itself contains all keys < key.
// key itself is not part of either tree.
// Note that after's parent is not changed; it must be set by the caller.
func splitExclusive[K, V any](m omap[K, V], key K) (after *node[K, V]) {
	pos, parent := m.find(key)
	if *pos == nil {
		*pos = &node[K, V]{parent: parent}
	}
	x := *pos
	x.pri = 0
	rotateUp(m, x)

	*m.root() = x.left
	if x.left != nil {
		x.left.parent = nil
	}
	return x.right
}

func markDeleted[K, V any](x *node[K, V]) {
	if x == nil {
		return
	}
	x.pri = 0
	markDeleted(x.left)
	markDeleted(x.right)
}

// All returns an iterator over the map m from smallest to largest key.
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *Map[K, V]) All() iter.Seq2[K, V] {
	return all(m)
}

// All returns an iterator over the map m from smallest to largest key.
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *MapFunc[K, V]) All() iter.Seq2[K, V] {
	return all(m)
}

// all returns an iterator over the map m from smallest to largest key, where *root is the root.
func all[K, V any](m omap[K, V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		x := *m.root()
		if x != nil {
			x = x.minNode()
		}
		for x != nil && yield(x.key, x.val) {
			x = x.next(m)
		}
	}
}

// Backward returns an iterator over the map m from largest to smallest key.
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *Map[K, V]) Backward() iter.Seq2[K, V] {
	return backward(m)
}

// Backward returns an iterator over the map m from largest to smallest key.
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *MapFunc[K, V]) Backward() iter.Seq2[K, V] {
	return backward(m)
}

// backward returns an iterator over the map m from largest to smallest key, where *root is the root.
func backward[K, V any](m omap[K, V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		x := *m.root()
		if x != nil {
			x = x.maxNode()
		}
		for x != nil && yield(x.key, x.val) {
			x = x.prev(m)
		}
	}
}

// Scan returns an iterator over the map m
// limited to keys k satisfying lo ≤ k ≤ hi.
//
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
// func (m *Map[K, V]) Scan(lo, hi K) iter.Seq2[K, V] {
// 	return func(yield func(K, V) bool) {
// 		x, _ := findGE(m, lo)
// 		for x != nil && x.key <= hi && yield(x.key, x.val) {
// 			x = x.next(m)
// 		}
// 	}
// }

// Scan returns an iterator over the map m
// limited to keys k satisfying lo ≤ k ≤ hi.
//
// If m is modified during the iteration, some keys may not be visited.
// No keys will be visited multiple times.
func (m *MapFunc[K, V]) Scan(lo, hi K) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		x, _ := findGE(m, lo)
		for x != nil && m.cmp(x.key, hi) <= 0 && yield(x.key, x.val) {
			x = x.next(m)
		}
	}
}

// next returns the successor node of x in the treap,
// even if x has been removed from the treap.
// x must not be nil.
func (x *node[K, V]) next(m omap[K, V]) *node[K, V] {
	if x.pri == 0 {
		// x has been deleted.
		// Find where x.key would be in the current tree.
		var eq bool
		x, eq = findGE(m, x.key)
		if !eq {
			// The new x is already greater than the old x.key.
			return x
		}
	}

	if x.right == nil {
		for x.parent != nil && x.parent.right == x {
			x = x.parent
		}
		return x.parent
	}
	return x.right.minNode()
}

// prev returns the predecessor node of x in the treap,
// even if x has been removed from the treap.
// x must not be nil.
func (x *node[K, V]) prev(m omap[K, V]) *node[K, V] {
	if x.pri == 0 {
		// x has been deleted.
		// Find where x.key would be in the current tree.
		var eq bool
		x, eq = findLE(m, x.key)
		if !eq {
			// The new x is already less than the old x.key.
			return x
		}
	}

	if x.left == nil {
		for x.parent != nil && x.parent.left == x {
			x = x.parent
		}
		return x.parent
	}
	return x.left.maxNode()
}

// findGE finds the node x in m with the least key k such that k ≥ key.
func findGE[K, V any](m omap[K, V], key K) (x *node[K, V], eq bool) {
	pos, parent := m.find(key)
	if *pos != nil {
		return *pos, true
	}
	if parent == nil {
		return nil, false
	}
	if pos == &parent.left {
		return parent, false
	}
	return parent.next(m), false
}

// findLE finds the node x in m with the greatest key k such that k ≤ key.
func findLE[K, V any](m omap[K, V], key K) (x *node[K, V], eq bool) {
	pos, parent := m.find(key)
	if *pos != nil {
		return *pos, true
	}
	if parent == nil {
		return nil, false
	}
	if pos == &parent.right {
		return parent, false
	}
	// Deleted nodes are detached from the tree, so the parent cannot be deleted
	// there will be no infinite recursion.
	assert(parent.pri != 0)
	return parent.prev(m), false
}

// rotateLeft rotates the subtree rooted at node x.
// turning (x a (y b c)) into (y (x a b) c).
func rotateLeft[K, V any](m omap[K, V], x *node[K, V]) {
	// p -> (x a (y b c))
	p := x.parent
	y := x.right
	b := y.left

	y.left = x
	x.parent = y
	x.right = b
	if b != nil {
		b.parent = x
	}

	y.parent = p
	if p == nil {
		*m.root() = y
	} else if p.left == x {
		p.left = y
	} else if p.right == x {
		p.right = y
	} else {
		// unreachable
		panic("corrupt treap")
	}
}

// rotateRight rotates the subtree rooted at node y.
// turning (y (x a b) c) into (x a (y b c)).
func rotateRight[K, V any](m omap[K, V], y *node[K, V]) {
	// p -> (y (x a b) c)
	p := y.parent
	x := y.left
	b := x.right

	x.right = y
	y.parent = x
	y.left = b
	if b != nil {
		b.parent = y
	}

	x.parent = p
	if p == nil {
		*m.root() = x
	} else if p.left == y {
		p.left = x
	} else if p.right == y {
		p.right = x
	} else {
		// unreachable
		panic("corrupt treap")
	}
}

// Clear deletes m[k] for all keys in m.
func (m *Map[K, V]) Clear() {
	m._root = nil
}

// Clear deletes m[k] for all keys in m.
func (m *MapFunc[K, V]) Clear() {
	m._root = nil
}

// Clone returns a copy of m.
func (m *Map[K, V]) Clone() *Map[K, V] {
	return &Map[K, V]{_root: m._root.clone(nil)}
}

// Clone returns a copy of m.
func (m *MapFunc[K, V]) Clone() *MapFunc[K, V] {
	m2 := NewMapFunc[K, V](m.cmp)
	m2._root = m._root.clone(nil)
	return m2
}

func (x *node[K, V]) clone(parent *node[K, V]) *node[K, V] {
	if x == nil {
		return nil
	}
	c := *x
	x2 := &c
	x2.left = x.left.clone(x2)
	x2.right = x.right.clone(x2)
	x2.parent = parent
	return x2
}

type Range[K cmp.Ordered, V any] struct {
	m      *Map[K, V]
	lo, hi bound[K]
}

func (r Range[K, V]) String() string {
	var b strings.Builder
	if !r.lo.present {
		b.WriteString("(-∞")
	} else {
		if r.lo.inclusive {
			b.WriteByte('[')
		} else {
			b.WriteByte('(')
		}
		fmt.Fprintf(&b, "%v", r.lo.key)
	}
	b.WriteString(", ")
	if !r.hi.present {
		b.WriteString("∞)")
	} else {
		fmt.Fprintf(&b, "%v", r.hi.key)
		if r.hi.inclusive {
			b.WriteByte(']')
		} else {
			b.WriteByte(')')
		}
	}
	return b.String()
}

type bound[K any] struct {
	key       K
	present   bool
	inclusive bool
}

func including[K any](k K) bound[K] {
	return bound[K]{k, true, true}
}

func excluding[K any](k K) bound[K] {
	return bound[K]{k, true, false}
}

func (m *Map[K, V]) From(lo K) Range[K, V]  { return Range[K, V]{m: m, lo: including(lo)} }
func (m *Map[K, V]) Above(lo K) Range[K, V] { return Range[K, V]{m: m, lo: excluding(lo)} }
func (m *Map[K, V]) To(hi K) Range[K, V]    { return Range[K, V]{m: m, hi: including(hi)} }
func (m *Map[K, V]) Below(hi K) Range[K, V] { return Range[K, V]{m: m, hi: excluding(hi)} }

func (r Range[K, V]) To(hi K) Range[K, V] {
	if r.hi.present {
		panic("range already has high bound")
	}
	r.hi = including(hi)
	return r
}

func (r Range[K, V]) Below(hi K) Range[K, V] {
	if r.hi.present {
		panic("range already has high bound")
	}
	r.hi = excluding(hi)
	return r
}

func (r Range[K, V]) inHi(k K) bool {
	if !r.hi.present {
		return true
	}
	if r.hi.inclusive {
		return k <= r.hi.key
	}
	return k < r.hi.key
}

func (r Range[K, V]) Min() (K, bool) {
	var z K
	if x := r.minNode(); x != nil {
		return x.key, true
	}
	return z, false
}

// minNode returns the node with the smallest key in r,
// or nil if r is empty.
func (r Range[K, V]) minNode() *node[K, V] {
	x := *r.m.root()
	if x == nil {
		return nil
	}
	if !r.lo.present {
		return x.minNode()
	}
	n, eq := findGE(r.m, r.lo.key)
	if eq && !r.lo.inclusive {
		n = n.next(r.m)
	}
	if n == nil || !r.inHi(n.key) {
		return nil
	}
	return n
}

// maxNode returns the node with the largest key in r,
// or nil if r is empty.
func (r Range[K, V]) maxNode() *node[K, V] {
	x := *r.m.root()
	if x == nil {
		return nil
	}
	if !r.lo.present {
		return x.minNode()
	}
	n, eq := findLE(r.m, r.hi.key)
	if eq && !r.lo.inclusive {
		n = n.next(r.m)
	}
	if n == nil || !r.inHi(n.key) {
		return nil
	}
	return n
}

// Clear deletes m[k] for all keys in r.
func (r Range[K, V]) Clear() {
	deleteRange(r.m, r.lo, r.hi)
}

func (r Range[K, V]) All() iter.Seq2[K, V] {
	x := *r.m.root()
	if !r.lo.present {
		x = x.minNode()
	} else {
		n, eq := findGE(r.m, r.lo.key)
		if eq && !r.lo.inclusive {
			n = n.next(r.m)
		}
		x = n
	}
	return func(yield func(K, V) bool) {
		for x != nil && r.inHi(x.key) && yield(x.key, x.val) {
			x = x.next(r.m)
		}
	}
}

func assert(b bool) {
	if !b {
		panic("assertion failed")
	}
}
