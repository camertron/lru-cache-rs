use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::{BuildHasherDefault, DefaultHasher, Hash, Hasher};

#[derive(Debug)]
struct Node<K, V> where K: Hash {
    hashed_key: u64,
    key: K,
    value: V,
    next_key: Option<u64>,
    prev_key: Option<u64>
}

pub struct LRUCacheIterator<'a, K, V> where K: 'a + Hash, V: 'a {
    cache: &'a LRUCache<K, V>,
    current: Option<u64>
}

impl<'a, K, V> Iterator for LRUCacheIterator<'a, K, V> where K: Hash {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.current.map(|hashed_key| {
            let node = self.cache.cache.get(&hashed_key).unwrap();
            self.current = node.next_key;
            (&node.key, &node.value)
        })
    }
}

#[derive(Debug)]
pub struct LRUCache<K, V> where K: Hash {
    capacity: usize,
    cache: HashMap<u64, Node<K, V>, BuildHasherDefault<IdentityHasher>>,
    head_key: Option<u64>,
    tail_key: Option<u64>
}

impl<'a, K: 'a + Hash, V: 'a> IntoIterator for &'a LRUCache<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = LRUCacheIterator<'a, K, V>;

    fn into_iter(self) -> LRUCacheIterator<'a, K, V> {
        LRUCacheIterator { cache: self, current: self.head_key }
    }
}

struct IdentityHasher {
    last_value: Option<u64>
}

impl Default for IdentityHasher {
    fn default() -> Self {
        IdentityHasher { last_value: None }
    }
}

impl Hasher for IdentityHasher {
    fn finish(&self) -> u64 {
        self.last_value.unwrap_or(0)
    }

    fn write(&mut self, bytes: &[u8]) {
        let sized_slice: &[u8; 8] = bytes.try_into().unwrap();
        self.last_value = Some(u64::from_le_bytes(*sized_slice));
    }
}

impl<K, V> LRUCache<K, V> where K: Hash {
    pub fn new(capacity: usize) -> Self {
        let cache = HashMap::<u64, Node<K, V>, BuildHasherDefault<IdentityHasher>>::default();
        LRUCache { capacity, cache, head_key: None, tail_key: None }
    }

    pub fn set(self: &mut Self, key: K, value: V) {
        let hashed_key = self.hash_key(&key);

        match self.delete_node(hashed_key) {
            Some(mut node) => {
                node.value = value;
                self.insert_node(node);
            },

            None => {
                self.insert(key, value);
            }
        }

        if self.cache.len() > self.capacity {
            self.delete_node(self.tail_key.unwrap());
        }
    }

    pub fn get(self: &mut Self, key: K) -> Option<&V> {
        let hashed_key = self.hash_key(&key);

        match self.delete_node(hashed_key) {
            Some(node) => {
                self.insert_node(node);
                self.get_node(&key).map(|node| &node.value)
            },

            None => None
        }
    }

    fn get_node(self: &Self, key: &K) -> Option<&Node<K, V>> {
        let hashed_key = self.hash_key(key);
        self.cache.get(&hashed_key)
    }

    pub fn delete(self: &mut Self, key: &K) -> bool {
        let hashed_key = self.hash_key(key);
        self.delete_node(hashed_key).is_some()
    }

    pub fn len(self: &Self) -> usize {
        self.cache.len()
    }

    pub fn keys(self: &Self) -> Vec<&K> {
        self.into_iter().map(|(k, _)| k).collect::<Vec<&K>>()
    }

    fn delete_node(self: &mut Self, hashed_key: u64) -> Option<Node<K, V>> {
        if let Some(node) = self.cache.remove(&hashed_key) {
            if node.prev_key.is_none() {
                // node is head
                self.head_key = node.next_key;

                if node.next_key.is_some() {
                    let next = self.cache.get_mut(&node.next_key.unwrap()).unwrap();
                    next.prev_key = None;
                }
            } else if node.next_key.is_none() {
                // node is tail
                if node.prev_key.is_some() {
                    let prev = self.cache.get_mut(&node.prev_key.unwrap()).unwrap();
                    prev.next_key = None;
                    self.tail_key = Some(prev.hashed_key);
                } else {
                    self.tail_key = None;
                }
            } else {
                // node is somewhere in the middle
                let prev_key = self.cache.get(&node.prev_key.unwrap()).unwrap().hashed_key;
                let next = self.cache.get_mut(&node.next_key.unwrap()).unwrap();
                next.prev_key = Some(prev_key);

                let next_key = self.cache.get(&node.next_key.unwrap()).unwrap().hashed_key;
                let prev = self.cache.get_mut(&node.prev_key.unwrap()).unwrap();
                prev.next_key = Some(next_key);
            }

            return Some(node);
        }

        None
    }

    fn insert(self: &mut Self, key: K, value: V) {
        let hashed_key = self.hash_key(&key);
        let new_node = Node { key, hashed_key, value, prev_key: None, next_key: None };
        self.insert_node(new_node);
    }

    fn insert_node(self: &mut Self, mut new_node: Node<K, V>) {
        match self.head_key {
            None => {
                self.head_key = Some(new_node.hashed_key);
                self.tail_key = Some(new_node.hashed_key);
                new_node.prev_key = None;
            },

            Some(head_key) => {
                let head = self.cache.get_mut(&head_key).unwrap();
                new_node.next_key = Some(head.hashed_key);
                new_node.prev_key = None;
                head.prev_key = Some(new_node.hashed_key);
                self.head_key = Some(new_node.hashed_key);
            }
        }

        self.cache.insert(new_node.hashed_key, new_node);
    }

    fn hash_key(self: &Self, key: &K) -> u64 {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }
}

impl<K, V> LRUCache<K, V> where K: Hash + Debug, V: Debug {
    fn to_string(self: &Self) -> String {
        let chunks = self
            .into_iter()
            .map(|(k, v)| { format!("{:?}: {:?}", k, v) })
            .collect::<Vec<String>>();

        format!("{{{}}}", chunks.join(", "))
    }
}

#[cfg(test)]
mod tests {
    use crate::LRUCache;

    #[test]
    fn allows_get_and_set_operations() {
        let mut cache: LRUCache<&str, &str> = LRUCache::new(5);
        cache.set("foo", "bar");
        assert!(cache.get("foo").is_some());
        assert!(cache.get("foo").unwrap() == &"bar");
    }

    #[test]
    fn get_returns_none_if_key_does_not_exist() {
        let mut cache: LRUCache<&str, &str> = LRUCache::new(5);
        assert!(cache.get("foo").is_none());
    }

    #[test]
    fn set_updates_value() {
        let mut cache: LRUCache<&str, &str> = LRUCache::new(5);

        cache.set("foo", "foo");
        cache.set("bar", "bar");
        cache.set("baz", "baz");
        assert!(cache.len() == 3);

        cache.set("foo", "foo2");
        assert!(cache.len() == 3);

        assert!(cache.get("foo").unwrap() == &"foo2");
    }

    #[test]
    fn allows_deleting_lru() {
        let mut cache: LRUCache<&str, &str> = LRUCache::new(5);
        cache.set("foo", "foo");
        cache.set("bar", "bar");
        cache.set("baz", "baz");
        assert!(cache.delete(&"foo"));
        assert!(cache.len() == 2);
        assert!(cache.keys() == vec![&"baz", &"bar"]);
    }

    #[test]
    fn allows_deleting_mru() {
        let mut cache: LRUCache<&str, &str> = LRUCache::new(5);
        cache.set("foo", "foo");
        cache.set("bar", "bar");
        cache.set("baz", "baz");
        assert!(cache.delete(&"baz"));
        assert!(cache.len() == 2);
        assert!(cache.keys() == vec![&"bar", &"foo"]);
    }

    #[test]
    fn allows_deleting_middle() {
        let mut cache: LRUCache<&str, &str> = LRUCache::new(5);
        cache.set("foo", "foo");
        cache.set("bar", "bar");
        cache.set("baz", "baz");
        assert!(cache.delete(&"bar"));
        assert!(cache.len() == 2);
        assert!(cache.keys() == vec![&"baz", &"foo"]);
    }

    #[test]
    fn allows_deleting_non_existent_item() {
        let mut cache: LRUCache<&str, &str> = LRUCache::new(5);
        cache.set("foo", "foo");
        assert!(!cache.delete(&"bar"));
        assert!(cache.len() == 1);
        assert!(cache.keys() == vec![&"foo"]);
    }

    #[test]
    fn evicts_lru_entry() {
        let mut cache: LRUCache<&str, &str> = LRUCache::new(3);
        cache.set("foo", "foo");
        cache.set("bar", "bar");
        cache.set("baz", "baz");
        cache.set("boo", "boo");  // should evict "foo"
        assert!(cache.len() == 3);
        assert!(cache.keys() == vec![&"boo", &"baz", &"bar"]);
    }

    #[test]
    fn promotes_lru_to_mru_on_get() {
        let mut cache: LRUCache<&str, &str> = LRUCache::new(5);

        cache.set("foo", "foo");
        cache.set("bar", "bar");
        cache.set("baz", "baz");
        assert!(cache.len() == 3);
        assert!(cache.keys() == vec![&"baz", &"bar", &"foo"]);

        cache.get("foo");
        assert!(cache.len() == 3);
        assert!(cache.keys() == vec![&"foo", &"baz", &"bar"]);
    }

    #[test]
    fn promotes_lru_to_mru_on_set() {
        let mut cache: LRUCache<&str, &str> = LRUCache::new(5);

        cache.set("foo", "foo");
        cache.set("bar", "bar");
        cache.set("baz", "baz");
        assert!(cache.len() == 3);
        assert!(cache.keys() == vec![&"baz", &"bar", &"foo"]);

        cache.set("foo", "foo");
        assert!(cache.len() == 3);
        assert!(cache.keys() == vec![&"foo", &"baz", &"bar"]);
    }
}

fn main() {
    let mut cache: LRUCache<&str, &str> = LRUCache::new(3);
    cache.set("foo", "foo val");
    cache.set("bar", "bar val");
    cache.set("baz", "baz_val");
    println!("{}", cache.to_string());

    cache.set("boo", "boo val");
    println!("foo should have been evicted:");
    println!("{}", cache.to_string());

    cache.set("bit", "bit val");
    println!("bar should have been evicted:");
    println!("{}", cache.to_string());
}
