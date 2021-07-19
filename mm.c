// Cezary Stajszczyk 317354
/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define debug(...) printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

typedef int32_t word_t;

static word_t *heap_end;
static word_t *heap_start;

static inline size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

/* requires pointer on payload */
static inline void set_header(word_t *payload, size_t size, bool is_allocated,
                              bool prev_free) {
  *(payload - 1) = size | prev_free << 1 | is_allocated;
}

/* require pointer on payload */
static inline void set_footer(word_t *payload, size_t size, bool is_allocated,
                              bool prev_free) {
  *(payload + size - 2) = size | prev_free << 1 | is_allocated;
}

/* requires poiner on boundary tag */
static inline int is_free(word_t *bt) {
  return !(*bt & 1);
}

/* requires poiner on boundary tag */
static inline int is_used(word_t *bt) {
  return *bt & 1;
}

/* requires pointer on payload */
static inline bool is_next_free(word_t *b) {
  return is_free((b - 1) + *(b - 1));
}

/* requires pointer on payload */
static inline bool is_prev_free(word_t *payload) {
  return *(payload - 1) & 2;
}

static inline void clr_prev_free(word_t *bt) {
  *bt &= ~2;
}

static inline void set_prev_free(word_t *bt) {
  *bt |= 2;
}

/* Returns block size (payload, header, footer and aligment included). Pointer
 * on bt */
static inline size_t get_size(word_t *bt) {
  return *bt & -4;
}

/* Returns address of next block or NULL. Requires pointer on header */
static inline word_t *next_block(word_t *bt) {
  if ((bt + get_size(bt)) > heap_end) {
    return NULL;
  }
  return bt + get_size(bt);
}

/* splits block  */
static inline void spliting(word_t *b, size_t size) {
  size_t new_size = get_size(b) - size;
  word_t *next = b + size + 1;
  set_header(next, new_size, false, false);
  set_footer(next, new_size, false, false);

  *(b + size + 1) = *(b + 1);
  *(b + size + 2) = *(b + 2);

  *(heap_start + *(b + 1) + 2) += size;
  *(heap_start + *(b + 2) + 1) += size;
}

/* add block to free blocks list */
static inline void add_block(word_t *bt) {
  if (*(heap_start + 1) == 0) {
    *(heap_start + 1) = bt - heap_start;
    *(heap_start + 2) = bt - heap_start;
    *(bt + 1) = 0;
    *(bt + 2) = 0;
  } else {
    word_t *block = heap_start + *(heap_start + 1);
    while (block) {
      if (get_size(bt) <= get_size(block)) {
        *(bt + 1) = *(heap_start + *(block + 2) + 1);
        *(bt + 2) = *(block + 2);
        *(block + 2) = bt - heap_start;
        *(heap_start + *(bt + 2) + 1) = bt - heap_start;
        return;
      }
      if (*(block + 1) == 0)
        break;
      block = heap_start + *(block + 1);
    }
    *(block + 1) = bt - heap_start;
    *(bt + 2) = block - heap_start;
    *(bt + 1) = 0;
    *(heap_start + 2) = bt - heap_start;
  }
}

/* pointer on header */
static inline void link_blocks(word_t *bt) {
  word_t *next = heap_start + *(bt + 1);
  word_t *prev = heap_start + *(bt + 2);

  *(prev + 1) = next - heap_start;
  *(next + 2) = prev - heap_start;
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
  /* Pad heap start so first payload is at ALIGNMENT. */
  if ((long)mem_sbrk(ALIGNMENT - sizeof(word_t)) < 0)
    return -1;

  heap_start = (word_t *)mem_heap_lo();
  heap_end = (word_t *)(mem_heap_hi() - 3);

  *heap_start = 0;
  *(heap_start + 1) = 0;
  *(heap_start + 2) = 0;

  return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size) {
  size = round_up(sizeof(word_t) + size);
  size_t max_size = get_size(heap_start + *(heap_start + 2));
  word_t *block = NULL;

  if (max_size < size / 4) {
    block = mem_sbrk(size);
    if ((long)block < 0)
      return NULL;

    set_header(++block, size / 4, true, false);

    heap_end += size / 4;

    return block;
  }
  
  if (*(heap_start + 1) != 0) {
    block = heap_start + *(heap_start + 1);
  }


  while (block) {
    if (is_free(block) && get_size(block) >= size / 4) {
      if (get_size(block) > size / 4) {
        spliting(block, size / 4);
      } else {
        link_blocks(block);
        word_t *next = next_block(block);
        if (next && !is_free(next))
          clr_prev_free(next);
      }

      set_header(++block, size / 4, true, false);

      return block;

    } else if (is_free(block) && !next_block(block)) {
      link_blocks(block);

      size_t add_size = round_up(size - 4 * get_size(block));
      if ((long)mem_sbrk(add_size) < 0)
        return NULL;

      heap_end += add_size / 4;
      set_header(block + 1, add_size / 4 + get_size(block), true, false);

      return ++block;
    }

    if (*(block + 1) != 0)
      block = heap_start + *(block + 1);
    else
      block = NULL;
  }

  block = mem_sbrk(size);
  if ((long)block < 0)
    return NULL;

  set_header(++block, size / 4, true, false);

  heap_end += size / 4;

  return block;
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr) {
  if (ptr == NULL)
    return;

  word_t *payload = (word_t *)ptr;
  word_t *bt = payload - 1;

  if (is_free(bt)) {
    fprintf(
      stderr,
      "ERROR: free failed. Attempt to free block which is already free.\n");
    exit(1);
  }

  word_t *prev = NULL;
  if (is_prev_free(payload)) {
    prev = bt - get_size(bt - 1);
  }
  word_t *next = next_block(bt);

  // case 1: (prev used  || prev == NULL) && (next used || next == NULL)
  if ((prev == NULL || is_used(prev)) && (next == NULL || is_used(next))) {
    *bt &= -4;             // header
    *(bt + *bt - 1) = *bt; // footer

    if (next) {
      set_prev_free(next);
    }
    add_block(bt);
    return;
  }

  // case 2: (prev used || prev == NULL) && next free
  if ((prev == NULL || is_used(prev)) && (next && is_free(next))) {
    link_blocks(next);

    *bt &= -4;             // header
    *(bt + *bt - 1) = *bt; // footer

    *bt += get_size(next); // scalanie
    *(bt + get_size(bt) - 1) = *bt;

    add_block(bt);
    return;
  }

  // case 3: prev free && (next used || next == NULL)
  if ((prev && is_free(prev) && (next == NULL || is_used(next)))) {
    if (next) {
      set_prev_free(next);
    }

    link_blocks(prev);

    *prev += get_size(bt);
    *(bt + get_size(bt) - 1) = *prev;

    add_block(prev);
    return;
  }

  // case 4: prev free && next free
  if ((prev && is_free(prev)) && (next && is_free(next))) {
    link_blocks(prev);
    link_blocks(next);

    *bt += get_size(next);          // scalanie
    *(bt + get_size(bt) - 1) = *bt; // z następnym

    *prev += get_size(bt);                // scalanie
    *(prev + get_size(prev) - 1) = *prev; // z poprzednim

    *prev &= -4;                 // header
    *(prev + *prev - 1) = *prev; // footer

    add_block(prev);
    return;
  }
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.
 **/
void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  word_t *block = (word_t *)old_ptr - 1;
  word_t *next = next_block(block);
  size_t old_size = get_size(block) * 4;

  /* Jeżeli zarządany rozmiar jest mniejszy lub równy aktualnemu */
  if (round_up(sizeof(word_t) + size) <= old_size) {
    return ++block;
  }

  /* Jeżeli zarządany rozmiar jest większy od aktualnego, ale po bloku jest
   * wystarczająco dużo wolnego miejsca */
  if (next && is_free(next) &&
      (old_size / 4 + get_size(next)) >=
        (round_up(sizeof(word_t) + size) / 4)) {
    link_blocks(next);
    *block += get_size(next);
    word_t *next2 = next_block(next);
    if (next2) {
      clr_prev_free(next2);
    }
    return ++block;
  }
  /* */

  void *new_ptr = malloc(size);
  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  /* Copy the old data. */
  if (size < old_size)
    old_size = size;
  memcpy(new_ptr, old_ptr, old_size);

  /* Free the old block. */
  free(old_ptr);

  return new_ptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

/*
 * mm_checkheap - So simple, it doesn't need a checker!
 */
void mm_checkheap(int verbose) {
  if (!verbose)
    return;

  word_t *block = heap_start + *(heap_start + 1);
  while (*(block + 1) != 0) {
    if (is_used(block))
      printf("\033[0;31mERROR:\033[0;37m na liście wolnych bloków znajduje się "
             "zajęty blok\n");
    block = heap_start + *(block + 1);
  }
}