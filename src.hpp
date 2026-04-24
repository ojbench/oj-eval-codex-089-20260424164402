// Buddy Allocator implementation for ACMOJ 2199
// Avoid STL containers to align with kernel-style constraints

namespace sjtu {

class BuddyAllocator {
public:
  BuddyAllocator(int ram_size, int min_block_size)
      : ram_size_(ram_size), min_block_size_(min_block_size), N_(0), L_(0),
        state_(nullptr) {
    // N_: number of minimal blocks (must be power of two)
    if (min_block_size_ <= 0)
      min_block_size_ = 1;
    if (ram_size_ < min_block_size_)
      ram_size_ = min_block_size_;

    N_ = ram_size_ / min_block_size_;
    // Ensure power of two (per problem guarantee). If not, round down to highest power of two.
    int n = 1;
    while ((n << 1) > 0 && (n << 1) <= N_) n <<= 1;
    if (n != N_) N_ = n;

    // Compute L_: log2(N_)
    L_ = 0;
    int t = N_;
    while (t > 1) {
      t >>= 1;
      ++L_;
    }

    // Tree uses 1-based indexing, up to 2*N_ - 1 nodes.
    // Allocate a bit more to be safe.
    tree_cap_ = (N_ << 2) + 8;
    state_ = new unsigned char[tree_cap_];
    for (int i = 0; i < tree_cap_; ++i) state_[i] = 0; // 0: UNUSED, 1: SPLIT, 2: FULL
    // Initially the whole memory is free (root UNUSED)
  }

  ~BuddyAllocator() {
    if (state_) {
      delete[] state_;
      state_ = nullptr;
    }
  }

  int malloc(int size) {
    if (!valid_size(size)) return -1;
    int order = order_from_size(size);
    int desired_depth = L_ - order;
    return alloc_first_node(1, 0, desired_depth, 0, N_);
  }

  int malloc_at(int addr, int size) {
    if (!valid_size(size)) return -1;
    if (addr < 0 || addr >= ram_size_) return -1;
    if (addr % size != 0) return -1; // must be aligned to size
    int order = order_from_size(size);
    int desired_depth = L_ - order;
    int leaf_start = addr / min_block_size_;
    if (leaf_start < 0 || leaf_start + (size / min_block_size_) > N_) return -1;
    return alloc_exact_node(1, 0, desired_depth, 0, N_, leaf_start);
  }

  void free_at(int addr, int size) {
    if (!valid_size(size)) return;
    if (addr < 0 || addr >= ram_size_) return;
    if (addr % size != 0) return;
    int order = order_from_size(size);
    int desired_depth = L_ - order;
    int leaf_start = addr / min_block_size_;
    (void)free_node(1, 0, desired_depth, 0, N_, leaf_start);
  }

private:
  // Internal representation
  // 0: UNUSED (entire block free, not split)
  // 1: SPLIT  (children exist; some/all parts may be allocated)
  // 2: FULL   (entire block allocated)

  int ram_size_;
  int min_block_size_;
  int N_;              // number of minimal blocks (power of two)
  int L_;              // levels from minimal to root: N_ = 2^L_
  int tree_cap_;
  unsigned char *state_;

  inline bool valid_size(int size) const {
    if (size <= 0) return false;
    if (size > ram_size_) return false;
    if ((size % min_block_size_) != 0) return false;
    int k = size / min_block_size_;
    // check power of two
    return (k & (k - 1)) == 0;
  }

  inline int order_from_size(int size) const {
    int k = size / min_block_size_;
    int order = 0;
    while (k > 1) {
      k >>= 1;
      ++order;
    }
    return order;
  }

  // Allocate leftmost available block at desired depth.
  int alloc_first_node(int idx, int depth, int desired_depth, int off, int span) {
    unsigned char st = state_[idx];
    if (st == 2) return -1; // FULL

    if (depth == desired_depth) {
      if (st == 0) { // UNUSED
        state_[idx] = 2; // FULL
        return off * min_block_size_;
      }
      // st == 1 (SPLIT) cannot allocate whole block here unless both children unused.
      // However, our operations maintain coalescing; conservative: fail.
      return -1;
    }

    // Need to go deeper
    if (st == 0) {
      // split
      state_[idx] = 1;
      state_[idx << 1] = 0;
      state_[(idx << 1) | 1] = 0;
    }

    int half = span >> 1;
    int res = alloc_first_node(idx << 1, depth + 1, desired_depth, off, half);
    if (res == -1) {
      res = alloc_first_node((idx << 1) | 1, depth + 1, desired_depth, off + half, half);
    }

    // Update current node state after attempts
    unsigned char l = state_[idx << 1];
    unsigned char r = state_[(idx << 1) | 1];
    if (l == 2 && r == 2) {
      state_[idx] = 2;
    } else if (l == 0 && r == 0) {
      // both children unused -> collapse back to UNUSED to avoid unnecessary splits
      state_[idx] = 0;
    } else {
      state_[idx] = 1;
    }
    return res;
  }

  // Allocate exactly the block whose leaf-start index equals target_start
  int alloc_exact_node(int idx, int depth, int desired_depth, int off, int span, int target_start) {
    unsigned char st = state_[idx];
    if (st == 2) return -1; // already fully allocated

    if (depth == desired_depth) {
      if (st == 0) {
        state_[idx] = 2;
        return target_start * min_block_size_;
      }
      // If split but subtree entirely free, we can coalesce and allocate
      if (st == 1 && subtree_free(idx)) {
        state_[idx] = 2;
        return target_start * min_block_size_;
      }
      return -1;
    }

    if (st == 0) {
      // split to descend
      state_[idx] = 1;
      state_[idx << 1] = 0;
      state_[(idx << 1) | 1] = 0;
    }

    int half = span >> 1;
    int res;
    if (target_start < off + half) {
      res = alloc_exact_node(idx << 1, depth + 1, desired_depth, off, half, target_start);
    } else {
      res = alloc_exact_node((idx << 1) | 1, depth + 1, desired_depth, off + half, half, target_start);
    }

    // Update state after child attempt
    unsigned char l = state_[idx << 1];
    unsigned char r = state_[(idx << 1) | 1];
    if (l == 2 && r == 2) {
      state_[idx] = 2;
    } else if (l == 0 && r == 0) {
      state_[idx] = 0;
    } else {
      state_[idx] = 1;
    }
    return res;
  }

  // Free the block at exact target node
  bool free_node(int idx, int depth, int desired_depth, int off, int span, int target_start) {
    unsigned char st = state_[idx];
    if (depth == desired_depth) {
      // The block must be allocated (FULL). If it is SPLIT, this would indicate
      // invalid free in our model; per problem statement, inputs are valid.
      state_[idx] = 0; // UNUSED
      return true;
    }

    if (st == 0) {
      // Freeing a deeper block under an UNUSED node should not happen for valid inputs.
      // To be robust, ensure children exist to continue.
      state_[idx] = 1;
      state_[idx << 1] = 0;
      state_[(idx << 1) | 1] = 0;
    } else if (st == 2) {
      // Parent fully allocated but freeing a child shouldn't occur with valid inputs.
      // Split to proceed robustly.
      state_[idx] = 1;
      state_[idx << 1] = 2;
      state_[(idx << 1) | 1] = 2;
    }

    int half = span >> 1;
    bool ok;
    if (target_start < off + half) {
      ok = free_node(idx << 1, depth + 1, desired_depth, off, half, target_start);
    } else {
      ok = free_node((idx << 1) | 1, depth + 1, desired_depth, off + half, half, target_start);
    }

    // After freeing child, update current node state with coalescing
    unsigned char l = state_[idx << 1];
    unsigned char r = state_[(idx << 1) | 1];
    if (l == 0 && r == 0) {
      state_[idx] = 0; // coalesce
    } else if (l == 2 && r == 2) {
      state_[idx] = 2;
    } else {
      state_[idx] = 1;
    }
    return ok;
  }

  // Check whether a subtree rooted at idx contains no allocations (entirely free)
  bool subtree_free(int idx) const {
    unsigned char st = state_[idx];
    if (st == 0) return true;
    if (st == 2) return false;
    // SPLIT: check children
    int l = idx << 1;
    int r = l | 1;
    // Guard against out-of-bounds in case of leaves represented as split
    if (l >= tree_cap_ || r >= tree_cap_) return false;
    return subtree_free(l) && subtree_free(r);
  }
};

} // namespace sjtu

