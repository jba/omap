// Copyright 2024 The Go Authors. All rights reserved.
//
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// TODO: rewrite deleteRange to avoid insertions.

// Package ordered implements an in-memory map whose
// keys are ordered.
package ordered

// The implementation is a treap. See:
// https://en.wikipedia.org/wiki/Treap
// https://faculty.washington.edu/aragon/pubs/rst89.pdf

import (
	"cmp"
	"fmt"
	"iter"
	"math/rand/v2"
	"strings"
)

// A _OMap is a map[K]V ordered according to K's standard Go ordering.
// The zero value of a _OMap is an empty _OMap ready to use.
type _OMap[K cmp.Ordered, V any] struct {
	_root *node[K, V]
	_gen  uint64
}

// A Map is a mapping from keys to values, where the keys are ordered according to
// an arbitrary comparison function.
// The zero value of a Map is not meaningful since it has no comparison function. Use [NewMap] to create a [Map].
// A nil *Map, like a nil Go map, can be read but not written and contains no entries.
type Map[K, V any] struct {
	_root *node[K, V]
	cmp   func(K, K) int
	_gen  uint64
}

// A node is a node in the treap.
type node[K any, V any] struct {
	parent *node[K, V]
	left   *node[K, V]
	right  *node[K, V]
	key    K
	val    V
	pri    uint64
	_size  int // number of keys in this node's subtree
}

// NewMap returns a new Map[K, V] ordered according to cmp.
func NewMap[K, V any](cmp func(K, K) int) *Map[K, V] {
	return &Map[K, V]{cmp: cmp}
}

// omap is the interface implemented by both Map[K, V] and MapFunc[K, V]
// that enables a common implementation of the map operations.
type omap[K, V any] interface {
	// root returns &m._root; the caller can read or write *m.root().
	root() **node[K, V]

	gen() uint64

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

func (m *_OMap[K, V]) root() **node[K, V] { return &m._root }
func (m *Map[K, V]) root() **node[K, V]   { return &m._root }

func (m *_OMap[K, V]) gen() uint64 { return m._gen }
func (m *Map[K, V]) gen() uint64   { return m._gen }

func (m *_OMap[K, V]) clear() { m.Clear() }
func (m *Map[K, V]) clear()   { m.Clear() }

func (m *_OMap[K, V]) get(k K) (V, bool) { return m.Get(k) }
func (m *Map[K, V]) get(k K) (V, bool)   { return m.Get(k) }

func (m *_OMap[K, V]) set(k K, v V) { m.Set(k, v) }
func (m *Map[K, V]) set(k K, v V)   { m.Set(k, v) }

// find looks up the key k in the map.
// It returns the parent of k as well as the position where k would be attached.
// *pos is non-nil if k is present, nil if k is missing.
// parent is nil if there are no nodes in the map, or if there is only one node and
// it's k.
func (m *_OMap[K, V]) find(k K) (pos **node[K, V], parent *node[K, V]) {
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
func (m *Map[K, V]) find(k K) (pos **node[K, V], parent *node[K, V]) {
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

// Contains reports whether the map contains an entry with the given key.
func (m *_OMap[K, V]) Contains(key K) bool {
	pos, _ := m.find(key)
	return *pos != nil
}

// Contains reports whether the map contains an entry with the given key.
func (m *Map[K, V]) Contains(key K) bool {
	pos, _ := m.find(key)
	return *pos != nil
}

// ContainsAll reports whether the map contains an entry for each key in the sequence.
func (m *_OMap[K, V]) ContainsAll(keys iter.Seq[K]) bool {
	for k := range m.Keys() {
		if !m.Contains(k) {
			return false
		}
	}
	return true
}

// ContainsAll reports whether the map contains an entry for each key in the sequence.
func (m *Map[K, V]) ContainsAll(keys iter.Seq[K]) bool {
	for k := range m.Keys() {
		if !m.Contains(k) {
			return false
		}
	}
	return true
}

// Get returns the value of m[key] and reports whether it exists.
func (m *_OMap[K, V]) Get(key K) (V, bool) {
	return get(m, key)
}

// Get returns the value of m[key] and reports whether it exists.
func (m *Map[K, V]) Get(key K) (V, bool) {
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

// At returns the value of m[key], or the zero value if key is not present.
func (m *_OMap[K, V]) At(key K) V {
	v, _ := get(m, key)
	return v
}

// At returns the value of m[key], or the zero value if key is not present.
func (m *Map[K, V]) At(key K) V {
	v, _ := get(m, key)
	return v
}

// Set sets m[key] = val.
// If the entry was present, Set returns the former value and false.
// Otherwise it returns the zero value and true.
func (m *_OMap[K, V]) Set(key K, val V) (old V, added bool) {
	return set(m, key, val)
}

// Set sets m[key] = val.
// If the entry was present, Set returns the former value and false.
// Otherwise it returns the zero value and true.
func (m *Map[K, V]) Set(key K, val V) (old V, added bool) {
	return set(m, key, val)
}

func set[K, V any](m omap[K, V], key K, val V) (V, bool) {
	pos, parent := m.find(key)
	if x := *pos; x != nil {
		old := x.val
		x.val = val
		return old, false
	}
	x := &node[K, V]{key: key, val: val, pri: rand.Uint64() | 1, parent: parent, _size: 1}
	*pos = x
	// Walk up, adjusting size.
	for p := x.parent; p != nil; p = p.parent {
		p._size++
	}

	rotateUp(m, x)
	var z V
	return z, true
}

// SetAll calls Set(k, v) for each key/value pair in the sequence.
// It reports whether the number of map entries increased.
func (m *Map[K, V]) SetAll(seq iter.Seq2[K, V]) bool {
	pre := m.Len()
	for k, v := range seq {
		m.Set(k, v)
	}
	return m.Len() > pre
}

func (m *_OMap[K, V]) SetAll(seq iter.Seq2[K, V]) bool {
	pre := m.Len()
	for k, v := range seq {
		m.Set(k, v)
	}
	return m.Len() > pre
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

// Delete removes the entry with the given key, if present.
// It reports whether the map changed, and returns the previous value,
// or the zero value if there isn't one.
func (m *_OMap[K, V]) Delete(key K) (V, bool) {
	return _delete(m, key)
}

// Delete removes the entry with the given key, if present.
// It reports whether the map changed, and returns the previous value, if any.
func (m *Map[K, V]) Delete(key K) (V, bool) {
	return _delete(m, key)
}

func _delete[K, V any](m omap[K, V], key K) (V, bool) {
	pos, _ := m.find(key)
	x := *pos
	if x == nil {
		var z V
		// TODO(jba): test prev
		return z, false
	}
	prev := x.val

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

	// Walk up, adjusting size.
	for p := x.parent; p != nil; p = p.parent {
		p._size--
	}

	// TODO(jba): test prev
	return prev, true
}

// DeleteAll removes all the entries whose keys are in the sequence.
// It reports whether the map changed.
func (m *_OMap[K, V]) DeleteAll(keys iter.Seq[K]) bool {
	return _deleteAll(m, keys)
}

// DeleteAll removes all the entries whose keys are in the sequence.
// It reports whether the map changed.
func (m *Map[K, V]) DeleteAll(keys iter.Seq[K]) bool {
	return _deleteAll(m, keys)
}

func _deleteAll[K, V any](m omap[K, V], seq iter.Seq[K]) bool {
	changed := false
	for k := range seq {
		if _, ok := _delete(m, k); ok {
			changed = true
		}
	}
	return changed
}

// Min returns the minimum key in m, its value, and true.
// If m is empty, the third return value is false.
func (m *_OMap[K, V]) Min() (K, V, bool) {
	return _min(m)
}

// Min returns the minimum key in m, its value, and true.
// If m is empty, the third return value is false.
func (m *Map[K, V]) Min() (K, V, bool) {
	return _min(m)
}

func _min[K, V any](m omap[K, V]) (K, V, bool) {
	x := *m.root()
	if x == nil {
		var zk K
		var zv V
		return zk, zv, false
	}
	n := x.minNode()
	return n.key, n.val, true
}

// minNode returns the node in x's subtree with the smallest key.
// x must not be nil.
func (x *node[K, V]) minNode() *node[K, V] {
	for x.left != nil {
		x = x.left
	}
	return x
}

// Max returns the maximum key in m, its value, and true.
// If m is empty, the third return value is false.
func (m *_OMap[K, V]) Max() (K, V, bool) {
	return _max(m)
}

// Max returns the maximum key in m, its value, and true.
// If m is empty, the third return value is false.
func (m *Map[K, V]) Max() (K, V, bool) {
	return _max(m)
}

func _max[K, V any](m omap[K, V]) (K, V, bool) {
	x := *m.root()
	if x == nil {
		var zk K
		var zv V
		return zk, zv, false
	}
	n := x.maxNode()
	return n.key, n.val, true
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
		m.clear() // TODO: avoid incrementing _gen twice
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
	_ = splitExclusive(m, lo)
	if after != nil {
		// Add after to m.
		// Both lo and all of after's keys are greater than any key in m.
		pos, parent := m.find(lo)
		assert(*pos == nil)
		*pos = after
		after.parent = parent
		// Adjust sizes.
		for p := parent; p != nil; p = p.parent {
			p.redoSize()
		}
		// after is now in the right place by key, but perhaps not by priority.
		rotateUp(m, after)
	}
}

func deleteAbove[K, V any](m omap[K, V], lo bound[K]) {
	assert(lo.present)
	val, ok := m.get(lo.key)
	_ = splitExclusive(m, lo.key)
	if !lo.inclusive && ok {
		m.set(lo.key, val)
	}
}

func deleteBelow[K, V any](m omap[K, V], hi bound[K]) {
	assert(hi.present)
	val, ok := m.get(hi.key)
	after := splitExclusive(m, hi.key)
	// Keep after, discard m.
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
	x._size = 0
	rotateUp(m, x)

	*m.root() = x.left
	if x.left != nil {
		x.left.parent = nil
	}
	return x.right
}

// All returns an iterator over the map m from smallest to largest key.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (m *_OMap[K, V]) All() iter.Seq2[K, V] {
	return all(m)
}

// All returns an iterator over the map m from smallest to largest key.
// If m is modified during the iteration,
// All guarantees that when a key is yielded, it is the successor of the key
// that was previously yielded (or the minimum key in the map, if it is the first
// key).
//
// For example, if the map contains keys 10 and 20, the iterator has yielded 10,
// and then 15 is inserted, then the next yielded key will be 15.
//
// Another example: if the map contains keys 10, 20 and 30, the iterator has yielded
// 10, and then 20 is deleted, then the next yielded key will be 30.
func (m *Map[K, V]) All() iter.Seq2[K, V] {
	return all(m)
}

// all returns an iterator over the map m from smallest to largest key, where *root is the root.
func all[K, V any](m omap[K, V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		x := *m.root()
		if x != nil {
			x = x.minNode()
		}
		gen := m.gen()
		for x != nil && yield(x.key, x.val) {
			x = x.next(m, gen != m.gen())
			gen = m.gen()
		}
	}
}

// Keys returns an iterator over the keys in m from smallest to largest.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (m *_OMap[K, V]) Keys() iter.Seq[K] {
	return keys(m)
}

// Keys returns an iterator over the keys in m from smallest to largest.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (m *Map[K, V]) Keys() iter.Seq[K] {
	return keys(m)
}

func keys[K, V any](m omap[K, V]) iter.Seq[K] {
	return func(yield func(K) bool) {
		x := *m.root()
		if x != nil {
			x = x.minNode()
		}
		gen := m.gen()
		for x != nil && yield(x.key) {
			x = x.next(m, gen != m.gen())
			gen = m.gen()
		}
	}
}

// Values returns an iterator over the values in m from smallest to largest key.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (m *_OMap[K, V]) Values() iter.Seq[V] {
	return values(m)
}

// Values returns an iterator over the values in m from smallest to largest key.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (m *Map[K, V]) Values() iter.Seq[V] {
	return values(m)
}

func values[K, V any](m omap[K, V]) iter.Seq[V] {
	return func(yield func(V) bool) {
		x := *m.root()
		if x != nil {
			x = x.minNode()
		}
		gen := m.gen()
		for x != nil && yield(x.val) {
			x = x.next(m, gen != m.gen())
			gen = m.gen()
		}
	}
}

// Backward returns an iterator over the map m from largest to smallest key.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (m *_OMap[K, V]) Backward() iter.Seq2[K, V] {
	return backward(m)
}

// Backward returns an iterator over the map m from largest to smallest key.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (m *Map[K, V]) Backward() iter.Seq2[K, V] {
	return backward(m)
}

// backward returns an iterator over the map m from largest to smallest key, where *root is the root.
func backward[K, V any](m omap[K, V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		x := *m.root()
		if x != nil {
			x = x.maxNode()
		}
		gen := m.gen()
		for x != nil && yield(x.key, x.val) {
			x = x.prev(m, gen != m.gen())
			gen = m.gen()
		}
	}
}

// backwardKeys returns an iterator over the keys in m from largest to smallest.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (m *_OMap[K, V]) backwardKeys() iter.Seq[K] {
	return backwardKeys(m)
}

// backwardKeys returns an iterator over the keys in m from largest to smallest.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (m *Map[K, V]) backwardKeys() iter.Seq[K] {
	return backwardKeys(m)
}

func backwardKeys[K, V any](m omap[K, V]) iter.Seq[K] {
	return func(yield func(K) bool) {
		x := *m.root()
		if x != nil {
			x = x.maxNode()
		}
		gen := m.gen()
		for x != nil && yield(x.key) {
			x = x.prev(m, gen != m.gen())
			gen = m.gen()
		}
	}
}

// backwardValues returns an iterator over the values in m from largest to smallest key.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (m *_OMap[K, V]) backwardValues() iter.Seq[V] {
	return backwardValues(m)
}

// backwardValues returns an iterator over the values in m from largest to smallest key.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (m *Map[K, V]) backwardValues() iter.Seq[V] {
	return backwardValues(m)
}

func backwardValues[K, V any](m omap[K, V]) iter.Seq[V] {
	return func(yield func(V) bool) {
		x := *m.root()
		if x != nil {
			x = x.maxNode()
		}
		gen := m.gen()
		for x != nil && yield(x.val) {
			x = x.prev(m, gen != m.gen())
			gen = m.gen()
		}
	}
}

// next returns the successor node of x in the treap,
// even if x has been removed from the treap.
// x must not be nil.
func (x *node[K, V]) next(m omap[K, V], reset bool) *node[K, V] {
	if x.pri == 0 || reset {
		// x has been deleted, or the iterator calling next has been invalidated.
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
func (x *node[K, V]) prev(m omap[K, V], reset bool) *node[K, V] {
	if x.pri == 0 || reset {
		// x has been deleted, or the iterator calling prev has been invalidated.
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
	return parent.next(m, false), false
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
	return parent.prev(m, false), false
}

func (x *node[K, V]) size() int {
	if x == nil {
		return 0
	}
	return x._size
}

// rank returns the position of x in its tree, counting from zero.
// x must not be nil.
func (x *node[K, V]) rank() int {
	if x == nil {
		panic("nil node")
	}
	r := x.left.size()
	for p := x.parent; p != nil; x, p = p, p.parent {
		if x == p.right {
			r += 1 + p.left.size()
		}
	}
	return r
}

func (x *node[K, V]) redoSize() {
	x._size = 1 + x.left.size() + x.right.size()
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

	// Recompute sizes bottom-up.
	x.redoSize()
	y.redoSize()
	// parent size doesn't change.
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

	// Recompute sizes bottom-up.
	y.redoSize()
	x.redoSize()
	// parent size doesn't change.
}

// Clear removes all entries from the map.
func (m *_OMap[K, V]) Clear() {
	m._root = nil
	m._gen++
}

// Clear removes all entries from the map.
func (m *Map[K, V]) Clear() {
	m._root = nil
	m._gen++
}

// Clone returns a shallow copy of m.
func (m *_OMap[K, V]) Clone() *_OMap[K, V] {
	return &_OMap[K, V]{_root: m._root.clone(nil)}
}

// Clone returns a shallow copy of m.
func (m *Map[K, V]) Clone() *Map[K, V] {
	m2 := NewMap[K, V](m.cmp)
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

// Len returns the number of keys in m.
func (m *_OMap[K, V]) Len() int { return m._root.size() }

// Len returns the number of keys in m.
func (m *Map[K, V]) Len() int { return m._root.size() }

// String returns a string representation of m in the form "{k1: v1, k2: v2}".
func (m *_OMap[K, V]) String() string {
	return mapString(m.All())
}

// String returns a string representation of m in the form "{k1: v1, k2: v2}".
func (m *Map[K, V]) String() string {
	return mapString(m.All())
}

func mapString[K, V any](items iter.Seq2[K, V]) string {
	var b strings.Builder
	b.WriteByte('{')
	first := true
	for k, v := range items {
		if !first {
			b.WriteString(", ")
		}
		first = false
		fmt.Fprintf(&b, "%v: %v", k, v)
	}
	b.WriteByte('}')
	return b.String()
}

// Nth returns the key and value at index i.
// It panics if i < 0 or i >= m.Len().
func (m *_OMap[K, V]) Nth(i int) (K, V) { return m._root.nth(i) }

// Nth returns the key and value at index i.
// It panics if i < 0 or i >= m.Len().
// See [Map.Index] for the inverse operation.
func (m *Map[K, V]) Nth(i int) (K, V) { return m._root.nth(i) }

// Index returns the index of key in m, or -1 if key is not present.
func (m *_OMap[K, V]) Index(key K) int {
	if m._root == nil {
		return -1
	}
	pos, _ := m.find(key)
	if *pos == nil {
		return -1
	}
	return (*pos).rank()
}

// Index returns the index of key in m, or -1 if key is not present.
// The index of a key is its position in the sequence of keys.
// For example, the smallest key has index 0,
// and the largest has index m.Len()-1.
// See [Map.Nth] for the inverse operation.
func (m *Map[K, V]) Index(key K) int {
	if m._root == nil {
		return -1
	}
	pos, _ := m.find(key)
	if *pos == nil {
		return -1
	}
	return (*pos).rank()
}

func (x *node[K, V]) nth(i int) (K, V) {
	if x == nil {
		panic("index out of range")
	}
	lsz := x.left.size()
	if i == lsz {
		return x.key, x.val
	}
	if i < lsz {
		return x.left.nth(i)
	}
	return x.right.nth(i - lsz - 1)
}

// From returns an _OMapSpan with lower bound lo, inclusive, and no upper bound.
func (m *_OMap[K, V]) From(lo K) _OMapSpan[K, V] {
	return _OMapSpan[K, V]{m: m, _lo: including(lo)}
}

// Above returns an _OMapSpan with lower bound lo, exclusive, and no upper bound.
func (m *_OMap[K, V]) Above(lo K) _OMapSpan[K, V] {
	return _OMapSpan[K, V]{m: m, _lo: excluding(lo)}
}

// To returns an _OMapSpan with upper bound hi, inclusive, and no lower bound.
func (m *_OMap[K, V]) To(hi K) _OMapSpan[K, V] {
	return _OMapSpan[K, V]{m: m, _hi: including(hi)}
}

// Below returns an _OMapSpan with upper bound hi, exclusive, and no lower bound.
func (m *_OMap[K, V]) Below(hi K) _OMapSpan[K, V] {
	return _OMapSpan[K, V]{m: m, _hi: excluding(hi)}
}

// From returns a MapSpan with lower bound lo, inclusive, and no upper bound.
func (m *Map[K, V]) From(lo K) MapSpan[K, V] { return MapSpan[K, V]{m: m, _lo: including(lo)} }

// Above returns a MapSpan with lower bound lo, exclusive, and no upper bound.
func (m *Map[K, V]) Above(lo K) MapSpan[K, V] { return MapSpan[K, V]{m: m, _lo: excluding(lo)} }

// To returns a MapSpan with upper bound hi, inclusive, and no lower bound.
func (m *Map[K, V]) To(hi K) MapSpan[K, V] { return MapSpan[K, V]{m: m, _hi: including(hi)} }

// Below returns a MapSpan with upper bound hi, exclusive, and no lower bound.
func (m *Map[K, V]) Below(hi K) MapSpan[K, V] { return MapSpan[K, V]{m: m, _hi: excluding(hi)} }

// A _OMapSpan is a subsequence of keys in an [_OMap].
type _OMapSpan[K cmp.Ordered, V any] struct {
	m        *_OMap[K, V]
	_lo, _hi bound[K]
}

// A MapSpan is a subsequence of keys in a [Map].
type MapSpan[K, V any] struct {
	m        *Map[K, V]
	_lo, _hi bound[K]
}

type _range[K, V any] interface {
	lo() bound[K]
	hi() bound[K]
	inHi(K) bool
	inLo(K) bool
	omap() omap[K, V]
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

func (s _OMapSpan[K, V]) omap() omap[K, V] { return s.m }
func (s MapSpan[K, V]) omap() omap[K, V]   { return s.m }

func (s _OMapSpan[K, V]) lo() bound[K] { return s._lo }
func (s MapSpan[K, V]) lo() bound[K]   { return s._lo }

func (s _OMapSpan[K, V]) hi() bound[K] { return s._hi }
func (s MapSpan[K, V]) hi() bound[K]   { return s._hi }

func (s _OMapSpan[K, V]) inHi(k K) bool {
	if !s._hi.present {
		return true
	}
	if s._hi.inclusive {
		return k <= s._hi.key
	}
	return k < s._hi.key
}

func (s _OMapSpan[K, V]) inLo(k K) bool {
	if !s._lo.present {
		return true
	}
	if s._lo.inclusive {
		return k >= s._lo.key
	}
	return k > s._lo.key
}

func (s MapSpan[K, V]) inHi(k K) bool {
	if !s._hi.present {
		return true
	}
	if s._hi.inclusive {
		return s.m.cmp(k, s._hi.key) <= 0
	}
	return s.m.cmp(k, s._hi.key) < 0
}

func (s MapSpan[K, V]) inLo(k K) bool {
	if !s._lo.present {
		return true
	}
	if s._lo.inclusive {
		return s.m.cmp(k, s._lo.key) >= 0
	}
	return s.m.cmp(k, s._lo.key) > 0
}

// To returns an _OMapSpan with upper bound hi, inclusive and the same lower bound as s.
func (s _OMapSpan[K, V]) To(hi K) _OMapSpan[K, V] {
	s._hi = including(hi)
	return s
}

// Below returns an _OMapSpan with upper bound hi, exclusive and the same lower bound as s.
func (s _OMapSpan[K, V]) Below(hi K) _OMapSpan[K, V] {
	s._hi = excluding(hi)
	return s
}

// From returns an _OMapSpan with lower bound lo, inclusive and the same upper bound as s.
func (s _OMapSpan[K, V]) From(lo K) _OMapSpan[K, V] {
	s._lo = including(lo)
	return s
}

// Above returns an _OMapSpan with lower bound lo, exclusive and the same upper bound as s.
func (s _OMapSpan[K, V]) Above(lo K) _OMapSpan[K, V] {
	s._lo = excluding(lo)
	return s
}

// To returns a MapSpan with upper bound hi, inclusive and the same lower bound as s,
// if hi is within s's current upper bound. Otherwise, it returns s.
func (s MapSpan[K, V]) To(hi K) MapSpan[K, V] {
	if s.inHi(hi) {
		s._hi = including(hi)
	}
	return s
}

// Below returns a MapSpan with upper bound hi, exclusive and the same lower bound as s,
// if hi is within s's current upper bound. Otherwise, it returns s.
func (s MapSpan[K, V]) Below(hi K) MapSpan[K, V] {
	if s.inHi(hi) {
		s._hi = excluding(hi)
	}
	return s
}

// From returns a MapSpan with lower bound lo, inclusive and the same upper bound as s,
// if lo is within s's current lower bound. Otherwise, it returns s.
func (s MapSpan[K, V]) From(lo K) MapSpan[K, V] {
	if s.inLo(lo) {
		s._lo = including(lo)
	}
	return s
}

// Above returns a MapSpan with lower bound lo, exclusive and the same upper bound as s,
// if lo is within s's current lower bound. Otherwise, it returns s.
func (s MapSpan[K, V]) Above(lo K) MapSpan[K, V] {
	if s.inLo(lo) {
		s._lo = excluding(lo)
	}
	return s
}

// Min returns the minimum key from r's underlying map that is in r, its value, and true.
// If m is empty, the third return value is false.
func (r _OMapSpan[K, V]) Min() (K, V, bool) { return rmin(r) }

// Min returns the minimum key from s's underlying map that is in s, its value, and true.
// If m is empty, the third return value is false.
func (s MapSpan[K, V]) Min() (K, V, bool) { return rmin(s) }

func rmin[K, V any](r _range[K, V]) (K, V, bool) {
	var zk K
	var zv V
	if x := minNode(r); x != nil {
		return x.key, x.val, true
	}
	return zk, zv, false
}

// minNode returns the node with the smallest key in r,
// or nil if r is empty.
func minNode[K, V any](r _range[K, V]) *node[K, V] {
	x := *r.omap().root()
	if x == nil {
		return nil
	}
	if !r.lo().present {
		x = x.minNode()
		if r.inHi(x.key) {
			return x
		}
		return nil
	}
	n, eq := findGE(r.omap(), r.lo().key)
	if eq && !r.lo().inclusive {
		n = n.next(r.omap(), false)
	}
	if n == nil || !r.inHi(n.key) {
		return nil
	}
	return n
}

// Max returns the maximum key from r's underlying map that is in r, its value, and true.
// If m is empty, the third return value is false.
func (r _OMapSpan[K, V]) Max() (K, V, bool) { return rmax(r) }

// Max returns the maximum key from r's underlying map that is in s, its value, and true.
// If m is empty, the third return value is false.
func (s MapSpan[K, V]) Max() (K, V, bool) { return rmax(s) }

// Index returns the index of key within r, or -1 if key is not present or not in bounds.
func (r _OMapSpan[K, V]) Index(key K) int { return rindex(r, key) }

// Index returns the index of key within s, or -1 if key is not present or not in bounds.
func (s MapSpan[K, V]) Index(key K) int { return rindex(s, key) }

// Len returns the number of keys in r.
func (r _OMapSpan[K, V]) Len() int { return rlen(r) }

// Len returns the number of keys in s.
func (s MapSpan[K, V]) Len() int { return rlen(s) }

func rlen[K, V any](r _range[K, V]) int {
	min := minNode(r)
	if min == nil {
		return 0
	}
	max := maxNode(r)
	if max == nil {
		return 0
	}
	return max.rank() - min.rank() + 1
}

func (s MapSpan[K, V]) String() string {
	return mapString(s.All())
}

func (s _OMapSpan[K, V]) String() string {
	return mapString(s.All())
}

// Nth returns the key and value at index i within r.
// It panics if i < 0 or i >= r.Len().
func (r _OMapSpan[K, V]) Nth(i int) (K, V) { return rnth(r, i) }

// Nth returns the key and value at index i within s.
// It panics if i < 0 or i >= s.Len().
func (s MapSpan[K, V]) Nth(i int) (K, V) { return rnth(s, i) }

func rnth[K, V any](r _range[K, V], i int) (K, V) {
	min := minNode(r)
	if min == nil {
		panic("index out of range")
	}
	return (*r.omap().root()).nth(min.rank() + i)
}

// Clone returns a new OMap containing only the keys in r.
func (r _OMapSpan[K, V]) Clone() *_OMap[K, V] {
	m := &_OMap[K, V]{}
	for k, v := range r.All() {
		m.Set(k, v)
	}
	return m
}

// Clone returns a new Map containing only the keys in s.
func (s MapSpan[K, V]) Clone() *Map[K, V] {
	m := NewMap[K, V](s.m.cmp)
	for k, v := range s.All() {
		m.Set(k, v)
	}
	return m
}

func rindex[K, V any](r _range[K, V], key K) int {
	if !r.inLo(key) || !r.inHi(key) {
		return -1
	}
	pos, _ := r.omap().find(key)
	if *pos == nil {
		return -1
	}
	min := minNode(r)
	if min == nil {
		return -1
	}
	return (*pos).rank() - min.rank()
}

func rmax[K, V any](r _range[K, V]) (K, V, bool) {
	var zk K
	var zv V
	if x := maxNode(r); x != nil {
		return x.key, x.val, true
	}
	return zk, zv, false
}

// maxNode returns the node with the largest key in r,
// or nil if r is empty.
func maxNode[K, V any](r _range[K, V]) *node[K, V] {
	x := *r.omap().root()
	if x == nil {
		return nil
	}
	if !r.hi().present {
		x = x.maxNode()
		if r.inLo(x.key) {
			return x
		}
		return nil
	}
	n, eq := findLE(r.omap(), r.hi().key)
	if eq && !r.hi().inclusive {
		n = n.prev(r.omap(), false)
	}
	if n == nil || !r.inLo(n.key) {
		return nil
	}
	return n
}

// Clear deletes all the entries in r from r's underlying map.
func (r _OMapSpan[K, V]) Clear() {
	deleteRange(r.m, r.lo(), r.hi())
	r.m._gen++
}

// Clear deletes all the entries in s from s's underlying map.
func (s MapSpan[K, V]) Clear() {
	deleteRange(s.m, s.lo(), s.hi())
	s.m._gen++
}

// All returns an iterator over r's underlying map from smallest to largest key in r.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (r _OMapSpan[K, V]) All() iter.Seq2[K, V] { return rall(r) }

// All returns an iterator over s's underlying map from smallest to largest key in s.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (s MapSpan[K, V]) All() iter.Seq2[K, V] { return rall(s) }

func rall[K, V any](r _range[K, V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		m := r.omap()
		x := *m.root()
		if x == nil {
			return
		}
		if !r.lo().present {
			x = x.minNode()
		} else {
			n, eq := findGE(m, r.lo().key)
			if eq && !r.lo().inclusive {
				n = n.next(m, false)
			}
			x = n
		}
		gen := m.gen()
		for x != nil && r.inHi(x.key) && yield(x.key, x.val) {
			x = x.next(m, gen != m.gen())
			gen = m.gen()
		}
	}
}

// Keys returns an iterator over the keys in r from smallest to largest.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (r _OMapSpan[K, V]) Keys() iter.Seq[K] { return rkeys(r) }

// Keys returns an iterator over the keys in s from smallest to largest.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (s MapSpan[K, V]) Keys() iter.Seq[K] { return rkeys(s) }

func rkeys[K, V any](r _range[K, V]) iter.Seq[K] {
	return func(yield func(K) bool) {
		m := r.omap()
		x := *m.root()
		if x == nil {
			return
		}
		if !r.lo().present {
			x = x.minNode()
		} else {
			n, eq := findGE(m, r.lo().key)
			if eq && !r.lo().inclusive {
				n = n.next(m, false)
			}
			x = n
		}
		gen := m.gen()
		for x != nil && r.inHi(x.key) && yield(x.key) {
			x = x.next(m, gen != m.gen())
			gen = m.gen()
		}
	}
}

// Values returns an iterator over the values in r from smallest to largest key.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (r _OMapSpan[K, V]) Values() iter.Seq[V] { return rvalues(r) }

// Values returns an iterator over the values in s from smallest to largest key.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (s MapSpan[K, V]) Values() iter.Seq[V] { return rvalues(s) }

func rvalues[K, V any](r _range[K, V]) iter.Seq[V] {
	return func(yield func(V) bool) {
		m := r.omap()
		x := *m.root()
		if x == nil {
			return
		}
		if !r.lo().present {
			x = x.minNode()
		} else {
			n, eq := findGE(m, r.lo().key)
			if eq && !r.lo().inclusive {
				n = n.next(m, false)
			}
			x = n
		}
		gen := m.gen()
		for x != nil && r.inHi(x.key) && yield(x.val) {
			x = x.next(m, gen != m.gen())
			gen = m.gen()
		}
	}
}

// Backward returns an iterator over r's underlying map from largest to smallest key in r.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (r _OMapSpan[K, V]) Backward() iter.Seq2[K, V] { return rbackward(r) }

// Backward returns an iterator over s's underlying map from largest to smallest key in s.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (s MapSpan[K, V]) Backward() iter.Seq2[K, V] { return rbackward(s) }

func rbackward[K, V any](r _range[K, V]) iter.Seq2[K, V] {
	return func(yield func(K, V) bool) {
		m := r.omap()
		x := *m.root()
		if x == nil {
			return
		}
		if !r.hi().present {
			x = x.maxNode()
		} else {
			n, eq := findLE(m, r.hi().key)
			if eq && !r.hi().inclusive {
				n = n.prev(m, false)
			}
			x = n
		}
		gen := m.gen()
		for x != nil && r.inLo(x.key) && yield(x.key, x.val) {
			x = x.prev(m, gen != m.gen())
			gen = m.gen()
		}
	}
}

// backwardKeys returns an iterator over the keys in r from largest to smallest.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (r _OMapSpan[K, V]) backwardKeys() iter.Seq[K] { return rbackwardKeys(r) }

// backwardKeys returns an iterator over the keys in s from largest to smallest.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (s MapSpan[K, V]) backwardKeys() iter.Seq[K] { return rbackwardKeys(s) }

func rbackwardKeys[K, V any](r _range[K, V]) iter.Seq[K] {
	return func(yield func(K) bool) {
		m := r.omap()
		x := *m.root()
		if x == nil {
			return
		}
		if !r.hi().present {
			x = x.maxNode()
		} else {
			n, eq := findLE(m, r.hi().key)
			if eq && !r.hi().inclusive {
				n = n.prev(m, false)
			}
			x = n
		}
		gen := m.gen()
		for x != nil && r.inLo(x.key) && yield(x.key) {
			x = x.prev(m, gen != m.gen())
			gen = m.gen()
		}
	}
}

// backwardValues returns an iterator over the values in r from largest to smallest key.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (r _OMapSpan[K, V]) backwardValues() iter.Seq[V] { return rbackwardValues(r) }

// backwardValues returns an iterator over the values in s from largest to smallest key.
// See [Map.All] for the guarantee provided if m is modified during the iteration.
func (s MapSpan[K, V]) backwardValues() iter.Seq[V] { return rbackwardValues(s) }

func rbackwardValues[K, V any](r _range[K, V]) iter.Seq[V] {
	return func(yield func(V) bool) {
		m := r.omap()
		x := *m.root()
		if x == nil {
			return
		}
		if !r.hi().present {
			x = x.maxNode()
		} else {
			n, eq := findLE(m, r.hi().key)
			if eq && !r.hi().inclusive {
				n = n.prev(m, false)
			}
			x = n
		}
		gen := m.gen()
		for x != nil && r.inLo(x.key) && yield(x.val) {
			x = x.prev(m, gen != m.gen())
			gen = m.gen()
		}
	}
}

func assert(b bool) {
	if !b {
		panic("assertion failed")
	}
}
