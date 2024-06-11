#pragma once

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <memory>

template <typename T, size_t SMALL_SIZE>
class socow_vector {
public:
  using value_type = T;

  using reference = T&;
  using const_reference = const T&;

  using pointer = T*;
  using const_pointer = const T*;

  using iterator = pointer;
  using const_iterator = const_pointer;

public:
  socow_vector() noexcept {}

  socow_vector(const socow_vector& other) : socow_vector(other, other.size()) {}

  socow_vector& operator=(const socow_vector& other) {
    if (this != &other) {
      if (other.static_storage()) {
        if (dynamic_storage()) {
          // possibly lose unique buffer, but get strong guarantee
          become_static(other.static_begin(), other.static_end());
        } else {
          if (size() <= other.size()) {
            std::uninitialized_copy(other.static_begin() + size(), other.static_end(), static_end());
            try {
              socow_vector tmp(other, size());
              std::swap_ranges(tmp.static_begin(), tmp.static_end(), static_begin());
            } catch (...) {
              std::destroy(static_end(), static_begin() + other.size());
              throw;
            }
          } else {
            socow_vector tmp(other);
            std::swap_ranges(tmp.static_begin(), tmp.static_end(), static_begin());
            std::destroy(static_begin() + other.size(), static_end());
          }
        }
      } else {
        destroy();
        share_buffer_with(other);
      }
      _size = other._size;
    }
    return *this;
  }

  ~socow_vector() noexcept {
    destroy();
  }

  reference operator[](size_t index) {
    return data()[index];
  }

  const_reference operator[](size_t index) const noexcept {
    return data()[index];
  }

  pointer data() {
    ensure_ownership();
    return raw_data();
  }

  const_pointer data() const noexcept {
    return raw_data();
  }

  size_t size() const noexcept {
    return _size;
  }

  reference front() {
    return data()[0];
  }

  const_reference front() const noexcept {
    return raw_data()[0];
  }

  reference back() {
    return data()[size() - 1];
  }

  const_reference back() const noexcept {
    return raw_data()[size() - 1];
  }

  void push_back(const T& value) {
    const size_t cap = capacity();
    if (cap == size()) {
      push_back_dynamic(value, cap == 0 ? 1 : cap * 2);
      _is_dynamic = true;
    } else if (dynamic_and_shared()) {
      push_back_dynamic(value, cap);
    } else {
      new (raw_end()) T(value);
    }
    _size++;
  }

  void pop_back() {
    ensure_ownership(size() - 1);
  }

  bool empty() const noexcept {
    return size() == 0;
  }

  size_t capacity() const noexcept {
    return static_storage() ? SMALL_SIZE : _buffer->capacity;
  }

  void reserve(size_t new_capacity) {
    if (new_capacity < size()) {
      return;
    }
    if (dynamic_and_shared() && SMALL_SIZE >= new_capacity) {
      become_static(dynamic_begin(), dynamic_end());
    } else if (dynamic_and_shared() || capacity() < new_capacity) {
      buffer* new_buf = copy_buffer(new_capacity);
      destroy();
      _buffer = new_buf;
      _is_dynamic = true;
    }
  }

  void shrink_to_fit() {
    if (static_storage() || size() == capacity()) {
      return;
    }
    force_ensure_ownership(size());
  }

  void clear() {
    ensure_ownership(0);
  }

  void swap(socow_vector& other) {
    if (this == &other) {
      return;
    }
    if (dynamic_storage() && other.dynamic_storage()) {
      std::swap(_buffer, other._buffer);
    } else if (static_storage() && other.static_storage()) {
      if (other.size() < size()) {
        std::uninitialized_copy(static_begin() + other.size(), static_end(), other.static_end());
        std::destroy(static_begin() + other.size(), static_end());
        std::swap(_size, other._size);
        std::swap_ranges(other.static_begin(), other.static_end(), static_begin());
      } else {
        other.swap(*this);
      }
      return;
    } else if (static_storage() && other.dynamic_storage()) {
      buffer* other_buf = other._buffer;
      try {
        other.copy_to_small(static_begin(), static_end());
      } catch (...) {
        other._buffer = other_buf;
        throw;
      }
      destroy_small();
      _buffer = other_buf;
      _is_dynamic = true;
    } else {
      other.swap(*this);
      return;
    }
    std::swap(_size, other._size);
  }

  iterator begin() {
    return data();
  }

  iterator end() {
    return data() + size();
  }

  const_iterator begin() const noexcept {
    return raw_data();
  }

  const_iterator end() const noexcept {
    return raw_data() + size();
  }

  iterator insert(const_iterator pos, const T& value) {
    const size_t cap = capacity();
    const ptrdiff_t dist = pos - raw_begin();
    if (cap == size()) {
      insert_dynamic(dist, value, cap == 0 ? 1 : cap * 2);
      _is_dynamic = true;
    } else if (dynamic_and_shared()) {
      insert_dynamic(dist, value, cap);
    } else {
      return in_place_insert(dist, value);
    }
    _size++;
    return raw_begin() + dist;
  }

  iterator erase(const_iterator pos) {
    return erase(pos, pos + 1);
  }

  iterator erase(const_iterator first, const_iterator last) {
    const ptrdiff_t count = last - first;
    const ptrdiff_t dist_first = first - raw_begin();
    const ptrdiff_t dist_last = last - raw_begin();
    const size_t new_size = size() - count;
    const iterator first_it = raw_begin() + dist_first;
    const iterator last_it = raw_begin() + dist_last;
    if (count == 0) {
      return last_it;
    }
    if (dynamic_and_shared()) {
      if (new_size <= SMALL_SIZE) {
        buffer* buf = _buffer;
        size_t copied = 0;
        try {
          std::uninitialized_copy(buf->data, first_it, static_begin());
          copied = dist_first;
          std::uninitialized_copy(last_it, buf->data + size(), static_begin() + copied);
        } catch (...) {
          std::destroy(static_begin(), static_begin() + copied);
          _buffer = buf;
          throw;
        }
        remove_ref(buf);
        _is_dynamic = false;
      } else {
        buffer* new_buf = new_buffer(new_size);
        size_t copied = 0;
        try {
          std::uninitialized_copy(dynamic_begin(), first_it, new_buf->data);
          copied = dist_first;
          std::uninitialized_copy(last_it, dynamic_end(), new_buf->data + copied);
        } catch (...) {
          delete_buffer(new_buf, copied);
          throw;
        }
        remove_ref();
        _buffer = new_buf;
      }
      _size = new_size;
    } else {
      in_place_erase(first_it, last_it);
    }
    return raw_begin() + dist_first;
  }

private:
  struct buffer {
    explicit buffer(size_t capacity) : capacity(capacity) {}

    std::size_t capacity;
    std::size_t ref_count = 1;
    T data[0];
  };

  std::size_t _size = 0;
  bool _is_dynamic = false;

  union {
    buffer* _buffer;
    T _small[SMALL_SIZE];
  };

private:
  socow_vector(const socow_vector& other, size_t size) : _size(size), _is_dynamic(other.dynamic_storage()) {
    if (other.static_storage()) {
      std::uninitialized_copy(other.static_begin(), other.static_begin() + size, static_begin());
    } else {
      assert(size == other.size());
      share_buffer_with(other);
    }
  }

  bool static_storage() const noexcept {
    return !dynamic_storage();
  }

  bool dynamic_storage() const noexcept {
    return _is_dynamic;
  }

  bool unique_buffer() const noexcept {
    assert(dynamic_storage());
    return _buffer->ref_count == 1;
  }

  bool shared_buffer() const noexcept {
    return !unique_buffer();
  }

  bool dynamic_and_unique() const noexcept {
    return dynamic_storage() && unique_buffer();
  }

  bool dynamic_and_shared() const noexcept {
    return dynamic_storage() && shared_buffer();
  }

  void copy_to_small(const_iterator first, const_iterator last) {
    std::uninitialized_copy(first, last, static_begin());
    _is_dynamic = false;
  }

  void become_static(const_iterator first, const_iterator last) {
    buffer* buf = _buffer;
    try {
      copy_to_small(first, last);
    } catch (...) {
      _buffer = buf;
      throw;
    }
    release_ref(buf);
  }

  void add_ref() const noexcept {
    assert(dynamic_storage());
    ++_buffer->ref_count;
  }

  static void remove_ref(buffer* buf) noexcept {
    assert(buf->ref_count > 1);
    --buf->ref_count;
  }

  void remove_ref() const noexcept {
    remove_ref(_buffer);
  }

  void release_ref(buffer* buf) const noexcept {
    if (--buf->ref_count == 0) {
      delete_buffer(buf, size());
    }
  }

  void release_ref() const noexcept {
    assert(dynamic_storage());
    release_ref(_buffer);
  }

  void release_ref_if_dynamic() noexcept {
    if (dynamic_storage()) {
      release_ref();
    }
  }

  static buffer* new_buffer(size_t capacity) {
    auto ptr = static_cast<buffer*>(operator new(sizeof(buffer) + sizeof(T) * capacity));
    return std::construct_at(ptr, capacity);
  }

  buffer* copy_buffer(size_t capacity) const {
    return copy_buffer(size(), capacity);
  }

  buffer* copy_buffer(size_t sz, size_t capacity) const {
    buffer* new_buf = new_buffer(capacity);
    try {
      std::uninitialized_copy(raw_begin(), raw_begin() + sz, new_buf->data);
    } catch (...) {
      remove_buffer(new_buf);
      throw;
    }
    return new_buf;
  }

  void delete_buffer(buffer* buf, size_t size) const noexcept {
    std::destroy(buf->data, buf->data + size);
    remove_buffer(buf);
  }

  void remove_buffer(buffer* buf) const noexcept {
    std::destroy_at(buf);
    operator delete(buf);
  }

  void destroy_small() noexcept {
    std::destroy(static_begin(), static_end());
  }

  void destroy() noexcept {
    if (dynamic_storage()) {
      release_ref();
    } else {
      destroy_small();
    }
  }

  void ensure_ownership() {
    ensure_ownership(size());
  }

  void ensure_ownership(size_t sz) {
    assert(sz <= size());
    if (static_storage() || unique_buffer()) {
      std::destroy(raw_begin() + sz, raw_end());
      _size = sz;
      return;
    }
    force_ensure_ownership(sz);
  }

  void force_ensure_ownership(size_t sz) {
    if (sz <= SMALL_SIZE) {
      become_static(dynamic_begin(), dynamic_begin() + sz);
    } else {
      buffer* new_buf = copy_buffer(sz, sz);
      release_ref_if_dynamic();
      _buffer = new_buf;
      _is_dynamic = true;
    }
    _size = sz;
  }

  void share_buffer_with(const socow_vector& other) noexcept {
    other.add_ref();
    _buffer = other._buffer;
    _is_dynamic = true;
  }

  iterator in_place_insert(size_t dist, const T& value) {
    new (raw_end()) T(value);
    ++_size;
    iterator it = raw_end() - 1;
    for (; it != raw_begin() + dist; --it) {
      std::swap(*it, *(it - 1));
    }
    return it;
  }

  void insert_dynamic(ptrdiff_t dist, const T& value, size_t capacity) {
    buffer* new_buf = new_buffer(capacity);
    size_t copied = 0;
    iterator it = raw_begin() + dist;
    try {
      std::uninitialized_copy(raw_begin(), it, new_buf->data);
      copied = dist;
      new (new_buf->data + copied) T(value);
      ++copied;
      std::uninitialized_copy(it, raw_end(), new_buf->data + copied);
    } catch (...) {
      delete_buffer(new_buf, copied);
      throw;
    }
    destroy();
    _buffer = new_buf;
  }

  void push_back_dynamic(const T& value, size_t capacity) {
    buffer* new_buf = copy_buffer(capacity);
    try {
      new (new_buf->data + size()) T(value);
    } catch (...) {
      delete_buffer(new_buf, size());
      throw;
    }
    destroy();
    _buffer = new_buf;
  }

  void in_place_erase(iterator first, iterator last) {
    const ptrdiff_t length = last - first;
    const iterator end = raw_end() - length;
    // ranges can overlap (cannot use swap_ranges)
    for (iterator it = first; it != end; ++it) {
      std::swap(*it, *(it + length));
    }
    std::destroy(end, raw_end());
    _size -= length;
  }

  iterator raw_begin() noexcept {
    return raw_data();
  }

  iterator raw_end() noexcept {
    return raw_data() + size();
  }

  const_iterator raw_begin() const noexcept {
    return raw_data();
  }

  const_iterator raw_end() const noexcept {
    return raw_data() + size();
  }

  pointer raw_data() noexcept {
    return dynamic_storage() ? _buffer->data : _small;
  }

  const_pointer raw_data() const noexcept {
    return dynamic_storage() ? _buffer->data : _small;
  }

  // can be used even if not static (to become static)
  pointer static_begin() noexcept {
    return _small;
  }

  pointer static_end() noexcept {
    return _small + size();
  }

  const_pointer static_begin() const noexcept {
    return _small;
  }

  const_pointer static_end() const noexcept {
    return _small + size();
  }

  pointer dynamic_begin() noexcept {
    assert(dynamic_storage());
    return _buffer->data;
  }

  pointer dynamic_end() noexcept {
    assert(dynamic_storage());
    return _buffer->data + size();
  }

  const_pointer dynamic_begin() const noexcept {
    assert(dynamic_storage());
    return _buffer->data;
  }

  const_pointer dynamic_end() const noexcept {
    assert(dynamic_storage());
    return _buffer->data + size();
  }
};
