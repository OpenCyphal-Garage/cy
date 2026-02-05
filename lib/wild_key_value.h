/// Source: https://github.com/pavel-kirienko/wild_key_value
///
/// Wild Key-Value is a fast and simple single-header key-value container with pattern matching for embedded systems.
/// Keys are strings, and values are void pointers.
/// Keys are stored in the heap in fragments; common prefixes are deduplicated so the memory usage is extremely low.
/// Patterns can be used to look up keys in the container, and also to look up patterns that match a given key;
/// the latter is called "routing".
///
/// WKV can be used with any memory manager that provides realloc. The standard realloc() is suitable, but the
/// recommended memory manager is O1Heap, which offers constant allocation time and low worst-case fragmentation.
///
/// This is the v1 release. When an API-incompatible v2 is published, all definitions will be prefixed with "wkv2"
/// instead of "wkv", and the file will be renamed to "wkv2.h" to ensure safe coexistence with the v1.
///
/// SEE ALSO
///
/// - O1Heap <https://github.com/pavel-kirienko/o1heap> -- a deterministic memory manager for real-time
///   high-integrity embedded systems.
/// - Cavl <https://github.com/pavel-kirienko/cavl> -- a single-header, efficient and robust AVL tree implementation.
///
/// LICENSE
///
/// Copyright (c) Pavel Kirienko <pavel@opencyphal.org>
///
/// Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated
/// documentation files (the "Software"), to deal in the Software without restriction, including without limitation
/// the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software,
/// and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
///
/// The above copyright notice and this permission notice shall be included in all copies or substantial portions of
/// the Software.
///
/// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE
/// WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS
/// OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
/// OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

// ReSharper disable CppCStyleCast CppZeroConstantCanBeReplacedWithNullptr
// ReSharper disable CppRedundantElaboratedTypeSpecifier CppRedundantInlineSpecifier
#pragma once

// ReSharper disable once CppUnusedIncludeDirective
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

/// If Wild Key-Value is used in throughput-critical code, then it is recommended to disable assertion checks
/// as they may be costly in terms of execution time.
#ifndef WKV_ASSERT
#if defined(WKV_NO_ASSERT) && WKV_NO_ASSERT
#define WKV_ASSERT(x) (void)0
#else
#include <assert.h>
#define WKV_ASSERT(x) assert(x)
#endif
#endif

#ifdef __cplusplus
// This is, strictly speaking, useless because we do not define any functions with external linkage here,
// but it tells static analyzers that what follows should be interpreted as C code rather than C++.
extern "C"
{
#endif

// ----------------------------------------         PUBLIC API SECTION         ----------------------------------------

/// These can be overridden at runtime on a per-container basis after wkv_init().
#define WKV_DEFAULT_SEPARATOR '/'
#define WKV_DEFAULT_SUB_ONE   '?'
#define WKV_DEFAULT_SUB_ANY   '*'

struct wkv_t;
struct wkv_edge_t;

#ifndef __cplusplus
typedef struct wkv_str_t          wkv_str_t;
typedef struct wkv_node_t         wkv_node_t;
typedef struct wkv_edge_t         wkv_edge_t;
typedef struct wkv_t              wkv_t;
typedef struct wkv_event_t        wkv_event_t;
typedef struct wkv_substitution_t wkv_substitution_t;
#endif

/// Wild Key-Value uses strings with explicit length for reasons of efficiency and safety.
/// Use wkv_key() to convert a C string into this type.
struct wkv_str_t
{
    size_t      len; ///< Length of the string, excluding the trailing NUL.
    const char* str; ///< This string may not be NUL-terminated!
};

/// A fundamental invariant of WKV is that every node has a value and/or outgoing edges. Nodes with neither are removed.
/// Setting the value to NULL manually may cause the node to be garbage collected at any time, so it must be avoided.
///
/// The user code MUST NOT change anything in this struct except the value pointer.
struct wkv_node_t
{
    wkv_node_t* parent; ///< NULL if this is the root node.

    size_t       n_edges;
    wkv_edge_t** edges; ///< Contiguous edge pointers ordered for bisection.

    /// The length of the full key of this node, excluding the trailing NUL, is needed for fast key reconstruction.
    /// We used to compute it ad-hoc by ascending the tree, which is easy, but is comparatively slow for such a basic
    /// operation. Keeping the length precomputed per node is a sensible trade-off.
    size_t key_len;
    void*  value; ///< NULL if this is not a full key.
};

/// The user code MUST NOT change anything here.
struct wkv_edge_t
{
    wkv_node_t node; ///< Base type.
    size_t     seg_len;
    /// This is a flex array; it may be shorter than this depending on the segment length.
    /// NUL terminator is NOT included here to conserve memory -- WKV does not need it.
    /// The size of seg is chosen rather arbitrarily; it has to be some sensible large value (over UINT16_MAX)
    /// to avoid UB triggered when we access memory beyond the struct footprint; see
    /// https://www.open-std.org/Jtc1/sc22/wg14/www/docs/dr_051.html
    char seg[1ULL << 16U];
};

/// When a new entry is inserted, Wild Key-Value needs to allocate tree nodes in the dynamic memory.
/// Each node with children takes one allocation (zero if no children); each edge takes one allocation always.
/// Per-edge allocation is of size sizeof(wkv_node_t) + sizeof(size_t) + strlen(key_segment).
/// Per-node allocation is of size n_edges * sizeof(pointer).
///
/// A key segment is the part of a key between separators (e.g. "abc" in "123/abc/456").
///
/// New memory is ONLY allocated from wkv_set().
///
/// Realloc is used as follows:
/// - Allocating new memory with the original pointer being NULL.
/// - Freeing memory when the new size is zero.
/// - Resizing existing allocation to a new size, which may be larger or smaller than the original size.
///
/// The semantics are per the standard realloc from stdlib, except that if the size is zero,
/// it must behave like free() (which is often the case in realloc() but technically an UB).
///
/// The recommended allocator is O1Heap: https://github.com/pavel-kirienko/o1heap
typedef void* (*wkv_realloc_t)(wkv_t* self, void* ptr, size_t new_size);

/// Once initialized, the instance shall not be moved or copied, as that breaks parent links in the tree.
/// Hint: pointer to a node with parent=NULL is the pointer to wkv_t of the current tree.
struct wkv_t
{
    wkv_node_t root; ///< Base type. Do not alter.

    /// See wkv_realloc_t.
    wkv_realloc_t realloc;

    /// The separator character used to split keys into segments. The default is WKV_DEFAULT_SEPARATOR.
    /// Can be changed to any non-zero character, but it should not be changed while the container is non-empty.
    char sep;

    /// The substitution characters can be changed at runtime to any non-zero character.
    /// Currently, we require each substitution token to be just a single character long.
    /// We could trivially allow multi-character substitution tokens by replacing these chars with wkv_str_t,
    /// but there doesn't appear to be a need for that at the moment, and this feature comes with a performance penalty.
    char sub_one; ///< Defaults to WKV_DEFAULT_SUB_ONE.
    char sub_any; ///< Defaults to WKV_DEFAULT_SUB_ANY.

    void* context; ///< Can be mutated by the user code arbitrarily.
};

// ----------------------------------------    INIT AND AUXILIARY FUNCTIONS    ----------------------------------------

/// Once created, the instance must not be moved, unless empty.
static inline void wkv_init(wkv_t* const self, const wkv_realloc_t realloc)
{
    WKV_ASSERT((self != NULL) && (realloc != NULL));
    memset(self, 0, sizeof(wkv_t));
    self->root.parent = NULL;
    self->root.edges  = NULL;
    self->root.value  = NULL;
    self->realloc     = realloc;
    self->sep         = WKV_DEFAULT_SEPARATOR;
    self->sub_one     = WKV_DEFAULT_SUB_ONE;
    self->sub_any     = WKV_DEFAULT_SUB_ANY;
    self->context     = NULL;
}

/// True if the container has no keys.
static inline bool wkv_is_empty(const wkv_t* const self)
{
    WKV_ASSERT(self != NULL);
    return self->root.n_edges == 0;
}

/// Writes the full key of the specified node into the buffer, with NUL termination.
/// The buffer shall be at least (node->key_len+1) bytes long.
/// This function is needed because WKV deduplicates common prefixes of keys, so full keys are not stored anywhere.
/// This function will rebuild the full key for this node on-demand; the complexity is linear in the key length
/// (sic! this is not much slower than bare memcpy!).
static inline void wkv_get_key(const wkv_t* const self, const wkv_node_t* const node, char* const buf)
{
    WKV_ASSERT((self != NULL) && (node != NULL) && (buf != NULL));
    char* p             = &buf[node->key_len];
    *p                  = '\0';
    const wkv_node_t* n = node;
    while (n->parent != NULL) {
        WKV_ASSERT(n->parent->n_edges > 0);
        const wkv_edge_t* const edge = (const wkv_edge_t*)n;
        WKV_ASSERT(edge->seg_len <= node->key_len);
        p -= edge->seg_len;
        WKV_ASSERT(p >= buf);
        memcpy(p, edge->seg, edge->seg_len);
        n = n->parent;
        if (n->parent != NULL) {
            *--p = self->sep;
        }
    }
    WKV_ASSERT((buf[node->key_len] == '\0') && (p == buf) && (strlen(p) == node->key_len));
}

/// Internally, WKV uses strings with explicit length for performance and safety reasons.
/// This helper converts a C string into a borrowed view wkv_str_t.
/// NULL strings are treated as empty strings.
static inline wkv_str_t wkv_key(const char* const str)
{
    const wkv_str_t out = {(str != NULL) ? strlen(str) : 0, str};
    return out;
}

/// Quickly checks if the key has any valid substitution tokens in it.
/// This can be used to discriminate between verbatim keys and match patterns.
static inline bool wkv_has_substitution_tokens(const wkv_t* const self, const wkv_str_t key);

// --------------------------------------    BASIC OPERATIONS ON VERBATIM KEYS    --------------------------------------

/// Creates a new entry and returns its node pointer. If such key already exists, then the existing node is returned.
/// If OOM or the key is too long, NULL is returned.
///
/// The caller is required to set the value pointer to a non-NULL value after this call; otherwise, the node may be
/// garbage collected at any time, or leaked when the container is destroyed.
///
/// This is the only function that may allocate new memory.
///
/// The key is treated verbatim (no pattern matching).
/// Complexity is logarithmic in the number of keys in the container.
static inline wkv_node_t* wkv_set(wkv_t* const self, const wkv_str_t key);

/// This is like wkv_set() except that it doesn't attempt to create a new node if the key does not exist,
/// returning NULL instead.
static inline wkv_node_t* wkv_get(const wkv_t* const self, const wkv_str_t key);

/// Deletes a known valid node. Does nothing if the node is NULL.
/// Behavior undefined if the node does not belong to the container.
/// The following is valid and safe:
///     wkv_del(&kv, wkv_get(&kv, wkv_key("key/name"))).
///
/// Complexity is logarithmic in the number of keys in the container.
static inline void wkv_del(wkv_t* const self, wkv_node_t* const node);

/// Returns the value and key of the element at the specified index, or NULL if the index is out of range.
/// The ordering is unspecified but stable between wkv_set() and wkv_del().
///
/// One could also use wkv_match() with the "*" pattern to list keys, but the difference here is that this function
/// works for keys composed of arbitrary characters, while wkv_match() assumes that certain characters (substitutions)
/// have special meaning.
///
/// Hint: one way to remove all keys from a container is:
///     while (!wkv_is_empty(&kv)) {
///         wkv_del(&kv, wkv_at(&kv, 0));
///     }
///
/// The complexity is linear in the number of keys in the container! This is not the primary way to access keys!
static inline wkv_node_t* wkv_at(wkv_t* const self, size_t index);

// ----------------------------------------          MATCH/ROUTE API          ----------------------------------------

/// Search patterns may contain substitution tokens. WKV currently recognizes the following substitutions:
///
/// -   One-segment substitution: "abc/?/def" -- matches "abc/123/def", with "123" being the substitution.
///     The substitution token must be the only text in the segment; otherwise, the segment is treated verbatim.
///
/// -   Any-segment substitution: "abc/*/def" -- matches any number of segments, including zero;
///     e.g. "abc/def", "abc/xyz/def", "abc/xyz/qwe/def".
///     There may be at most one any-segment substitution token in the pattern; if more are found,
///     the following occurrences are treated verbatim (no substitution will take place).
///     This behavior, however, should not be relied upon because it may change in a future minor revision;
///     hence, patterns with multiple any-segment substitutions should be avoided.
///     The substitution token must be the only text in the segment; otherwise, the segment is treated verbatim.
///
/// The reason for allowing at most one any-segment substitution is that multiple occurrences may result in ambiguous
/// patterns, which in certain scenarios may match the same key multiple times, plus it causes fast complexity growth.
/// It is difficult to avoid these issues without a significant performance and memory penalty,
/// hence the limitation is imposed.
///
/// Hint: a sequence of "?/*" is similar to the glob recursive wildcard "**".
///
/// When a pattern match occurs, WKV provides a list of substitutions that had to be made to match the key against
/// the pattern; this is conceptually similar to capture groups in regular expressions.
/// The elements are ordered in the same way as they appear in the pattern, and each element specifies which
/// substitution token it is produced for via 'ordinal'.
///
/// For example, pattern "abc/?/def/*" matching "abc/123/def/foo/456/xyz" produces the following substitution list,
/// with the ordinals as specified:
/// 1. #0 "123"
/// 2. #1 "foo"
/// 3. #1 "456"
/// 4. #1 "xyz"
///
/// Another example: pattern "abc/*/def" matching "abc/def" produces no substitutions.
struct wkv_substitution_t
{
    wkv_str_t           str;     ///< The string that matched the substitution token in the pattern.
    size_t              ordinal; ///< Zero-based index of the substitution token as occurred in the pattern.
    wkv_substitution_t* next;    ///< Next substitution in the linked list, NULL if this is the last one.
};

struct wkv_event_t
{
    wkv_t* self;

    /// The node is never NULL.
    /// Use node->value to read/modify the value.
    /// Use wkv_get_key() to get the key.
    wkv_node_t* node;

    /// The substitutions indicate which segments of the key matched corresponding substitution tokens in the pattern.
    /// NULL substitutions indicate that the substitution list is empty.
    /// The substitution_count is for convenience; note that this is a linked list, not a contiguous array.
    /// The substitutions pointer is invalidated after the callback returns.
    size_t                    substitution_count;
    const wkv_substitution_t* substitutions;

    void* context;
};

/// Invoked on every positive result while searching.
/// Searching stops when this function returns a non-NULL value, which is then propagated back to the caller.
typedef void* (*wkv_callback_t)(wkv_event_t);

/// Searches for keys in the container that match the specified pattern.
/// Matching elements are reported in an unspecified order.
///
/// Searching stops when callback returns a non-NULL value, which is then propagated back to the caller.
/// If no matches are found or callback returns NULL for all matches, then NULL is returned.
///
/// The computational complexity depends on the query. If the query contains no substitution tokens,
/// the complexity is logarithmic in the number of keys in the container. Any-segment substitutions
/// are the hardest to evaluate unless positioned at the end of the pattern.
static inline void* wkv_match(wkv_t* const         self,
                              const wkv_str_t      query,
                              void* const          context,
                              const wkv_callback_t callback);

/// Searches for patterns in the container that match the specified key.
/// Matching elements are reported in an unspecified order.
///
/// Searching stops when callback returns a non-NULL value, which is then propagated back to the caller.
/// If no matches are found or callback returns NULL for all matches, then NULL is returned.
///
/// The computational complexity depends on the keys in the container. If none of the patterns in the container
/// contain substitution tokens, then the complexity is logarithmic in the number of patterns in the container.
static inline void* wkv_route(wkv_t* const         self,
                              const wkv_str_t      query,
                              void* const          context,
                              const wkv_callback_t callback);

// ====================================================================================================================
// ----------------------------------------     END OF PUBLIC API SECTION      ----------------------------------------
// ====================================================================================================================
// ----------------------------------------      POLICE LINE DO NOT CROSS      ----------------------------------------
// ====================================================================================================================

static inline void _wkv_free(wkv_t* const self, void* const ptr)
{
    if (ptr != NULL) {
        (void)self->realloc(self, ptr, 0);
    }
}

static inline wkv_str_t _wkv_edge_seg(const wkv_edge_t* const edge)
{
    const wkv_str_t out = {edge->seg_len, edge->seg};
    return out;
}

typedef struct
{
    wkv_str_t head;
    wkv_str_t tail;
    bool      last;
} _wkv_split_t;

static inline _wkv_split_t _wkv_split(const wkv_str_t key, const char sep)
{
    WKV_ASSERT(key.str != NULL);
    const char* const slash   = (const char*)memchr(key.str, sep, key.len);
    const size_t      seg_len = (slash != NULL) ? (size_t)(slash - key.str) : key.len;
    _wkv_split_t      out     = {{seg_len, key.str}, {0, ""}, slash == NULL};
    if (slash != NULL) {
        out.tail.str = slash + 1;
        out.tail.len = key.len - seg_len - 1U;
    }
    return out;
}

/// Allocates the edge and its key segment in the same dynamically-sized memory block.
static wkv_edge_t* _wkv_edge_new(wkv_t* const self, wkv_node_t* const parent, const wkv_str_t seg)
{
    wkv_edge_t* const edge = (wkv_edge_t*)self->realloc(self, NULL, offsetof(wkv_edge_t, seg) + seg.len);
    if (edge != NULL) {
        edge->node.parent  = parent;
        edge->node.n_edges = 0;
        edge->node.edges   = NULL;
        edge->node.value   = NULL;
        edge->seg_len      = seg.len;
        memcpy(&edge->seg[0], seg.str, seg.len);
    }
    return edge;
}

/// Returns negated (insertion point plus one) if the segment is not found.
static ptrdiff_t _wkv_bisect(const wkv_node_t* const node, const wkv_str_t seg)
{
    size_t lo = 0;
    size_t hi = node->n_edges;
    while (lo < hi) {
        const size_t mid = (lo + hi) / 2U;
        // Ultra-fast comparison thanks to knowing the length of both segments.
        // IMPORTANT: because of the length comparison shortcut, the ordering is not lexicographic!
        const ptrdiff_t cmp = (seg.len == node->edges[mid]->seg_len)
                                ? memcmp(seg.str, node->edges[mid]->seg, seg.len)
                                : ((ptrdiff_t)seg.len - (ptrdiff_t)node->edges[mid]->seg_len);
        if (cmp == 0) {
            return (ptrdiff_t)mid;
        }
        if (cmp < 0) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    return -(((ptrdiff_t)lo) + 1); // insertion point; +1 is to handle the case of zero index insertion
}

/// Returns the index of the edge pointing to this node in the parent's edge array.
/// If the node is the root, then -1 is returned.
static ptrdiff_t _wkv_locate_in_parent(wkv_node_t* const node)
{
    const wkv_node_t* const parent = node->parent;
    if (parent != NULL) {
        const wkv_edge_t* const edge = (wkv_edge_t*)node;
        const ptrdiff_t         k    = _wkv_bisect(parent, _wkv_edge_seg(edge));
        WKV_ASSERT((k >= 0) && (k < (ptrdiff_t)parent->n_edges));
        WKV_ASSERT(parent->edges[k] == edge);
        return k;
    }
    return -1; // The root node has no parent.
}

/// Downsize the edges pointer array of the node to the current number of edges.
/// Infallible: if shrinking fails, keep using the existing allocation because it remains valid and is large enough.
static inline void _wkv_shrink(wkv_t* const self, wkv_node_t* const node)
{
    if (node->edges != NULL) {
        const size_t       new_size = node->n_edges * sizeof(wkv_edge_t*);
        wkv_edge_t** const shrunk   = (wkv_edge_t**)self->realloc(self, (void*)node->edges, new_size);
        if (new_size == 0U) {
            node->edges = NULL;
        } else if (shrunk != NULL) {
            node->edges = shrunk;
        } else {
            (void)0; // realloc failed to shrink, keep using the original (larger) block.
        }
    }
}

/// Starting from a leaf node, go up the tree and remove all nodes whose trace does not eventually lead to a full key.
/// This is intended for aborting insertions when we run out of memory and have to backtrack.
static inline void _wkv_prune_branch(wkv_t* const self, wkv_node_t* const node)
{
    _wkv_shrink(self, node);
    if ((node->n_edges == 0) && (node->value == NULL)) {
        const ptrdiff_t k = _wkv_locate_in_parent(node);
        if (k >= 0) {
            wkv_node_t* const p = node->parent;
            WKV_ASSERT(p != NULL);
            // Remove the edge from the parent's edge array. It will be shrunk in the next recursion level.
            p->n_edges--;
            memmove(&p->edges[k], &p->edges[k + 1], (p->n_edges - (size_t)k) * sizeof(wkv_edge_t*));
            // Free the edge and its segment. We use the node pointer which is the same as the edge pointer.
            _wkv_free(self, node->edges); // This is probably NULL bc empty, but we don't enforce this.
            _wkv_free(self, node);
            // Removing the node from the parent may have caused the parent to become eligible for garbage collection.
            _wkv_prune_branch(self, p);
        }
        // If the node is not eligible for garbage collection, then all its parents are not eligible either,
        // which means there is nothing left to do.
    }
}

/// Locates or creates a new node, but does not alter it.
static inline wkv_node_t* _wkv_find_or_insert(wkv_t* const self, const wkv_str_t key)
{
    wkv_node_t*  n = &self->root;
    _wkv_split_t x;
    x.tail = key; // Start with the full key.
    do {
        x           = _wkv_split(x.tail, self->sep);
        ptrdiff_t k = _wkv_bisect(n, x.head);
        if (k < 0) { // Insort the new edge.
            k = -(k + 1);
            WKV_ASSERT((k >= 0) && (k <= (ptrdiff_t)n->n_edges));
            // Expand the edge pointer array and allocate the new edge. This may fail, which will require backtracking.
            wkv_edge_t* new_e = NULL;
            {
                wkv_edge_t** const new_edges =
                  (wkv_edge_t**)self->realloc(self, n->edges, (n->n_edges + 1) * sizeof(wkv_edge_t*));
                if (new_edges != NULL) {
                    n->edges = new_edges; // Will be shrunk later if necessary.
                    new_e    = _wkv_edge_new(self, n, x.head);
                }
            }
            if (NULL == new_e) {
                _wkv_prune_branch(self, n); // We may have inserted transient nodes that are now garbage. Clean them up.
                return NULL;
            }
            WKV_ASSERT(n->edges != NULL);
            memmove(&n->edges[k + 1], &n->edges[k], (n->n_edges - (size_t)k) * sizeof(wkv_edge_t*));
            n->edges[k] = new_e;
            n->n_edges++;
        }
        WKV_ASSERT((n->edges != NULL) && (n == n->edges[k]->node.parent));
        n = &n->edges[k]->node;
    } while (!x.last);
    WKV_ASSERT(n != NULL);
    return n;
}

/// Will return empty nodes as well! Not suitable for direct API exposure.
static inline wkv_node_t* _wkv_get(const wkv_t* const self, const wkv_node_t* const node, const wkv_str_t key)
{
    const _wkv_split_t x = _wkv_split(key, self->sep);
    const ptrdiff_t    k = _wkv_bisect(node, x.head);
    if (k >= 0) {
        WKV_ASSERT((size_t)k < node->n_edges);
        wkv_edge_t* const edge = node->edges[k];
        WKV_ASSERT((edge != NULL) && (edge->node.parent == node));
        return x.last ? &edge->node : _wkv_get(self, &edge->node, x.tail);
    }
    return NULL;
}

static inline wkv_node_t* _wkv_at(wkv_node_t* const node, size_t* const index)
{
    if (node->value != NULL) {
        if (*index == 0) {
            return node;
        }
        --*index;
    }
    for (size_t i = 0; i < node->n_edges; ++i) {
        wkv_node_t* const child = _wkv_at(&node->edges[i]->node, index);
        if (child != NULL) {
            return child;
        }
    }
    return NULL;
}

static inline wkv_node_t* wkv_set(wkv_t* const self, const wkv_str_t key)
{
    WKV_ASSERT(self != NULL);
    wkv_node_t* const node = _wkv_find_or_insert(self, key);
    if (node != NULL) {
        if (node->value == NULL) {
            node->key_len = key.len;
        }
        WKV_ASSERT(node->key_len == key.len);
    }
    return node;
}

static inline wkv_node_t* wkv_get(const wkv_t* const self, const wkv_str_t key)
{
    WKV_ASSERT(self != NULL);
    wkv_node_t* const node = _wkv_get(self, &self->root, key);
    WKV_ASSERT((node == NULL) || (node->value == NULL) || (node->key_len == key.len));
    // Do not return valueless nodes! The user must create those explicitly first.
    return ((node == NULL) || (node->value == NULL)) ? NULL : node;
}

static inline void wkv_del(wkv_t* const self, wkv_node_t* const node)
{
    WKV_ASSERT(self != NULL);
    if ((node != NULL) && (node->parent != NULL)) {
        node->value = NULL;
        _wkv_prune_branch(self, node);
    }
}

static inline wkv_node_t* wkv_at(wkv_t* const self, size_t index)
{
    WKV_ASSERT(self != NULL);
    return _wkv_at(&self->root, &index);
}

static inline bool wkv_has_substitution_tokens(const wkv_t* const self, const wkv_str_t key)
{
    const _wkv_split_t x = _wkv_split(key, self->sep);
    if ((x.head.len == 1) && ((x.head.str[0] == self->sub_one) || (x.head.str[0] == self->sub_any))) {
        return true;
    }
    return x.last ? false : wkv_has_substitution_tokens(self, x.tail); // tail call
}

// ---------------------------------    FAST PATTERN MATCHING / KEY ROUTING ENGINE     ---------------------------------

typedef struct
{
    wkv_t*         self;
    void*          context;
    wkv_callback_t callback;
} _wkv_hit_ctx_t;

typedef struct
{
    wkv_substitution_t* head;
    wkv_substitution_t* tail;
    size_t              count;
} _wkv_substitution_list_t;

static inline void* _wkv_hit_node(const _wkv_hit_ctx_t* const           ctx,
                                  wkv_node_t* const                     node,
                                  const _wkv_substitution_list_t* const subs)
{
    const wkv_event_t evt = {ctx->self, node, subs->count, subs->head, ctx->context};
    return (node->value != NULL) ? ctx->callback(evt) : NULL;
}

/// This is to avoid boilerplate in the substitution token handlers.
#define _wkv_SUBSTITUTION_PUSH(old_list, new_list, str, ordinal)       \
    WKV_ASSERT(ordinal >= 0);                                          \
    wkv_substitution_t new_list##_tail = {str, (size_t)ordinal, NULL}; \
    if (old_list.tail != NULL) {                                       \
        old_list.tail->next = &new_list##_tail;                        \
    }                                                                  \
    const _wkv_substitution_list_t new_list = {                        \
      (old_list.head == NULL) ? &new_list##_tail : old_list.head,      \
      &new_list##_tail,                                                \
      old_list.count + 1,                                              \
    };                                                                 \
    (void)0

/// Substitutions are stack-allocated, so we must unlink entries when leaving a stack frame.
#define _wkv_SUBSTITUTION_POP(list) \
    if (list.tail != NULL) {        \
        list.tail->next = NULL;     \
    }                               \
    (void)0

// MATCH

/// Currently, we DO NOT support removal of nodes from the callback, for the sole reason that removal
/// would invalidate our edges traversal state. This can be doctored, if necessary.
/// The initial substitution ordinal shall be -1.
static inline void* _wkv_match(const _wkv_hit_ctx_t* const    ctx,
                               const wkv_node_t* const        node,
                               const _wkv_split_t             qs,
                               const ptrdiff_t                sub_ord,
                               const _wkv_substitution_list_t subs,
                               const bool                     any_seen);

/// Matches one-segment substitution: a/?/b
static inline void* _wkv_match_sub_one(const _wkv_hit_ctx_t* const    ctx,
                                       const wkv_node_t* const        node,
                                       const _wkv_split_t             qs,
                                       const ptrdiff_t                sub_ord,
                                       const _wkv_substitution_list_t subs,
                                       const bool                     any_seen)
{
    WKV_ASSERT((subs.tail == NULL) || (subs.tail->next == NULL));
    void*              result  = NULL;
    const _wkv_split_t qs_next = qs.last ? qs : _wkv_split(qs.tail, ctx->self->sep);
    for (size_t i = 0; (i < node->n_edges) && (result == NULL); ++i) {
        wkv_edge_t* const edge = node->edges[i];
        _wkv_SUBSTITUTION_PUSH(subs, subs_new, _wkv_edge_seg(edge), sub_ord);
        result = qs.last ? _wkv_hit_node(ctx, &edge->node, &subs_new)
                         : _wkv_match(ctx, &edge->node, qs_next, sub_ord, subs_new, any_seen);
        _wkv_SUBSTITUTION_POP(subs);
    }
    return result;
}

/// Matches many-segment substitution (one or more): a/+/b ==> a/?/b, a/?/?/b, a/?/?/?/b, ...
static inline void* _wkv_match_sub_many(const _wkv_hit_ctx_t* const    ctx,
                                        const wkv_node_t* const        node,
                                        const _wkv_split_t             qs,
                                        const ptrdiff_t                sub_ord,
                                        const _wkv_substitution_list_t subs)
{
    WKV_ASSERT((subs.tail == NULL) || (subs.tail->next == NULL));
    const _wkv_split_t qs_next = qs.last ? qs : _wkv_split(qs.tail, ctx->self->sep);
    void*              result  = NULL;
    for (size_t i = 0; (i < node->n_edges) && (result == NULL); ++i) {
        wkv_edge_t* const edge = node->edges[i];
        _wkv_SUBSTITUTION_PUSH(subs, subs_new, _wkv_edge_seg(edge), sub_ord);
        result = qs.last ? _wkv_hit_node(ctx, &edge->node, &subs_new)
                         : _wkv_match(ctx, &edge->node, qs_next, sub_ord, subs_new, true);
        if (result == NULL) {
            subs_new.tail->next = NULL;
            result              = _wkv_match_sub_many(ctx, &edge->node, qs, sub_ord, subs_new);
        }
        _wkv_SUBSTITUTION_POP(subs);
    }
    return result;
}

/// Matches any-segment substitution (zero or more): a/*/b ==> a/b, a/?/b, a/?/?/b, ...
static inline void* _wkv_match_sub_any(const _wkv_hit_ctx_t* const    ctx,
                                       const wkv_node_t* const        node,
                                       const _wkv_split_t             qs,
                                       const ptrdiff_t                sub_ord,
                                       const _wkv_substitution_list_t subs)
{
    WKV_ASSERT((subs.tail == NULL) || (subs.tail->next == NULL));
    void* result = qs.last ? NULL : _wkv_match(ctx, node, _wkv_split(qs.tail, ctx->self->sep), sub_ord, subs, true);
    if (result == NULL) {
        result = _wkv_match_sub_many(ctx, node, qs, sub_ord, subs);
    }
    return result;
}

static inline void* _wkv_match(const _wkv_hit_ctx_t* const    ctx,
                               const wkv_node_t* const        node,
                               const _wkv_split_t             qs,
                               const ptrdiff_t                sub_ord,
                               const _wkv_substitution_list_t subs,
                               const bool                     any_seen)
{
    WKV_ASSERT((subs.tail == NULL) || (subs.tail->next == NULL));
    const bool x_any = (qs.head.len == 1) && (qs.head.str[0] == ctx->self->sub_any) && (!any_seen);
    const bool x_one = (qs.head.len == 1) && (qs.head.str[0] == ctx->self->sub_one);
    if (x_one) {
        return _wkv_match_sub_one(ctx, node, qs, sub_ord + 1, subs, any_seen);
    }
    if (x_any) {
        return _wkv_match_sub_any(ctx, node, qs, sub_ord + 1, subs);
    }
    const ptrdiff_t k = _wkv_bisect(node, qs.head);
    if (k >= 0) {
        wkv_edge_t* const edge = node->edges[k];
        return qs.last ? _wkv_hit_node(ctx, &edge->node, &subs)
                       : _wkv_match(ctx, &edge->node, _wkv_split(qs.tail, ctx->self->sep), sub_ord, subs, any_seen);
    }
    return NULL;
}

// ROUTE

/// The any_seen is used to track occurrences of the any-segment substitution pattern in the path.
/// We do not allow more than one per path to manage the search complexity and avoid double-matching the query key.
/// The initial substitution ordinal shall be -1.
static inline void* _wkv_route(const _wkv_hit_ctx_t* const    ctx,
                               const wkv_node_t* const        node,
                               const _wkv_split_t             qs,
                               const ptrdiff_t                sub_ord,
                               const _wkv_substitution_list_t subs,
                               const bool                     any_seen);

static inline void* _wkv_route_sub_one(const _wkv_hit_ctx_t* const    ctx,
                                       wkv_edge_t* const              edge,
                                       const _wkv_split_t             qs,
                                       const ptrdiff_t                sub_ord,
                                       const _wkv_substitution_list_t subs,
                                       const bool                     any_seen)
{
    WKV_ASSERT((subs.tail == NULL) || (subs.tail->next == NULL));
    _wkv_SUBSTITUTION_PUSH(subs, subs_new, qs.head, sub_ord);
    void* const result =
      qs.last ? _wkv_hit_node(ctx, &edge->node, &subs_new)
              : _wkv_route(ctx, &edge->node, _wkv_split(qs.tail, ctx->self->sep), sub_ord, subs_new, any_seen);
    _wkv_SUBSTITUTION_POP(subs);
    return result;
}

static inline void* _wkv_route_sub_any(const _wkv_hit_ctx_t* const    ctx,
                                       wkv_edge_t* const              edge,
                                       const _wkv_split_t             qs,
                                       const ptrdiff_t                sub_ord,
                                       const _wkv_substitution_list_t subs)
{
    WKV_ASSERT((subs.tail == NULL) || (subs.tail->next == NULL));
    void* result = _wkv_route(ctx, &edge->node, qs, sub_ord, subs, true);
    if (result == NULL) {
        _wkv_SUBSTITUTION_PUSH(subs, subs_new, qs.head, sub_ord);
        result = qs.last ? _wkv_hit_node(ctx, &edge->node, &subs_new)
                         : _wkv_route_sub_any(ctx, edge, _wkv_split(qs.tail, ctx->self->sep), sub_ord, subs_new);
        _wkv_SUBSTITUTION_POP(subs);
    }
    return result;
}

static inline void* _wkv_route(const _wkv_hit_ctx_t* const    ctx,
                               const wkv_node_t* const        node,
                               const _wkv_split_t             qs,
                               const ptrdiff_t                sub_ord,
                               const _wkv_substitution_list_t subs,
                               const bool                     any_seen)
{
    WKV_ASSERT((subs.tail == NULL) || (subs.tail->next == NULL));
    void* result = NULL;
    {
        const wkv_str_t sub_one = {1, &ctx->self->sub_one};
        const ptrdiff_t k       = _wkv_bisect(node, sub_one);
        if (k >= 0) {
            result = _wkv_route_sub_one(ctx, node->edges[k], qs, sub_ord + 1, subs, any_seen);
        }
    }
    if ((result == NULL) && (!any_seen)) {
        const wkv_str_t sub_any = {1, &ctx->self->sub_any};
        const ptrdiff_t k       = _wkv_bisect(node, sub_any);
        if (k >= 0) {
            result = _wkv_route_sub_any(ctx, node->edges[k], qs, sub_ord + 1, subs);
        }
    }
    if (result == NULL) {
        const ptrdiff_t k = _wkv_bisect(node, qs.head);
        if (k >= 0) {
            wkv_edge_t* const edge = node->edges[k];
            // _wkv_route() is a tail call
            result = qs.last
                       ? _wkv_hit_node(ctx, &edge->node, &subs)
                       : _wkv_route(ctx, &edge->node, _wkv_split(qs.tail, ctx->self->sep), sub_ord, subs, any_seen);
        }
    }
    return result;
}

// ----------------------------------------        wkv_match / wkv_route        ----------------------------------------

static inline void* wkv_match(wkv_t* const         self,
                              const wkv_str_t      query,
                              void* const          context,
                              const wkv_callback_t callback)
{
    const _wkv_hit_ctx_t           ctx  = {self, context, callback};
    const _wkv_substitution_list_t subs = {NULL, NULL, 0};
    return _wkv_match(&ctx, &self->root, _wkv_split(query, self->sep), -1, subs, false);
}

static inline void* wkv_route(wkv_t* const         self,
                              const wkv_str_t      query,
                              void* const          context,
                              const wkv_callback_t callback)
{
    const _wkv_hit_ctx_t           ctx  = {self, context, callback};
    const _wkv_substitution_list_t subs = {NULL, NULL, 0};
    return _wkv_route(&ctx, &self->root, _wkv_split(query, self->sep), -1, subs, false);
}

#ifdef __cplusplus
}
#endif
