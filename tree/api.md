type Map[K, V any] struct {
func NewMap[K, V any](cmp func(K, K) int) *Map[K, V]
func (m *Map[K, V]) Above(lo K) Range[K, V]
func (m *Map[K, V]) All() iter.Seq2[K, V]
func (m *Map[K, V]) At(key K) V
func (m *Map[K, V]) Backward() iter.Seq2[K, V]
func (m *Map[K, V]) Below(hi K) Range[K, V]
func (m *Map[K, V]) Clear()
func (m *Map[K, V]) Clone() *Map[K, V]
func (m *Map[K, V]) Delete(key K) bool
func (m *Map[K, V]) From(lo K) Range[K, V]
func (m *Map[K, V]) Get(key K) (V, bool)
func (m *Map[K, V]) Index(key K) int
func (m *Map[K, V]) Keys() iter.Seq[K]
func (m *Map[K, V]) Len() int
func (m *Map[K, V]) Max() (K, V, bool)
func (m *Map[K, V]) Min() (K, V, bool)
func (m *Map[K, V]) Nth(i int) (K, V)
func (m *Map[K, V]) Set(key K, val V) (old V, added bool)
func (m *Map[K, V]) String() string
func (m *Map[K, V]) To(hi K) Range[K, V]
func (m *Map[K, V]) Values() iter.Seq[V]
type OMap[K cmp.Ordered, V any] struct {
func (m *OMap[K, V]) Above(lo K) ORange[K, V]
func (m *OMap[K, V]) All() iter.Seq2[K, V]
func (m *OMap[K, V]) At(key K) V
func (m *OMap[K, V]) Backward() iter.Seq2[K, V]
func (m *OMap[K, V]) Below(hi K) ORange[K, V]
func (m *OMap[K, V]) Clear()
func (m *OMap[K, V]) Clone() *OMap[K, V]
func (m *OMap[K, V]) Delete(key K) bool
func (m *OMap[K, V]) From(lo K) ORange[K, V]
func (m *OMap[K, V]) Get(key K) (V, bool)
func (m *OMap[K, V]) Index(key K) int
func (m *OMap[K, V]) Keys() iter.Seq[K]
func (m *OMap[K, V]) Len() int
func (m *OMap[K, V]) Max() (K, V, bool)
func (m *OMap[K, V]) Min() (K, V, bool)
func (m *OMap[K, V]) Nth(i int) (K, V)
func (m *OMap[K, V]) Set(key K, val V) (old V, added bool)
func (m *OMap[K, V]) String() string
func (m *OMap[K, V]) To(hi K) ORange[K, V]
func (m *OMap[K, V]) Values() iter.Seq[V]
type ORange[K cmp.Ordered, V any] struct {
func (r ORange[K, V]) All() iter.Seq2[K, V]
func (r ORange[K, V]) Backward() iter.Seq2[K, V]
func (r ORange[K, V]) Below(hi K) ORange[K, V]
func (r ORange[K, V]) Clear()
func (r ORange[K, V]) Clone() *OMap[K, V]
func (r ORange[K, V]) Index(key K) int
func (r ORange[K, V]) Keys() iter.Seq[K]
func (r ORange[K, V]) Len() int
func (r ORange[K, V]) Max() (K, V, bool)
func (r ORange[K, V]) Min() (K, V, bool)
func (r ORange[K, V]) Nth(i int) (K, V)
func (r ORange[K, V]) To(hi K) ORange[K, V]
func (r ORange[K, V]) Values() iter.Seq[V]
type Range[K, V any] struct {
func (r Range[K, V]) All() iter.Seq2[K, V]
func (r Range[K, V]) Backward() iter.Seq2[K, V]
func (r Range[K, V]) Below(hi K) Range[K, V]
func (r Range[K, V]) Clear()
func (r Range[K, V]) Clone() *Map[K, V]
func (r Range[K, V]) Index(key K) int
func (r Range[K, V]) Keys() iter.Seq[K]
func (r Range[K, V]) Len() int
func (r Range[K, V]) Max() (K, V, bool)
func (r Range[K, V]) Min() (K, V, bool)
func (r Range[K, V]) Nth(i int) (K, V)
func (r Range[K, V]) To(hi K) Range[K, V]
func (r Range[K, V]) Values() iter.Seq[V]
