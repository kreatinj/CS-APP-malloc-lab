/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit intoa word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Given block ptr pb, compute address of its header and footer */
#define HDRP(bp) ((void *)(bp) - WSIZE)

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(HDRP(p)) & ~0x7)
#define GET_ALLOC(p) (GET(HDRP(p)) & 0x1)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((void *)(bp) + GET_SIZE(bp))

static void *heap_listp;

static void *find_prev_block(void *bp)
{
    void *ptr;
    for (ptr = heap_listp; GET_SIZE(ptr) > 0; ptr = NEXT_BLKP(ptr))
        if (NEXT_BLKP(ptr) == bp)
            return ptr;
    return NULL;
}

static void *coalesce(void *bp)
{
    void *prev_blkp = find_prev_block(bp);

    size_t prev_alloc = prev_blkp ? GET_ALLOC(prev_blkp) : 1;
    size_t next_alloc = GET_ALLOC(NEXT_BLKP(bp));
    size_t size = GET_SIZE(bp);

    if (prev_alloc && next_alloc)
        return bp;

    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(NEXT_BLKP(bp));
        PUT(HDRP(NEXT_BLKP(bp)), 0);
        PUT(HDRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(prev_blkp);
        PUT(HDRP(prev_blkp), PACK(size, 0));
        PUT(HDRP(bp), 0);
        bp = prev_blkp;
    }

    else
    {
        size += GET_SIZE(prev_blkp) + GET_SIZE(NEXT_BLKP(bp));
        PUT(HDRP(prev_blkp), PACK(size, 0));
        PUT(HDRP(NEXT_BLKP(bp)), 0);
        PUT(HDRP(bp), 0);
        bp = prev_blkp;
    }

    return bp;
}

static void *extend_heap(size_t words)
{
    void *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void *find_fit(size_t asize)
{
    /* First-fit search */
    void *bp;

    for (bp = heap_listp; GET_SIZE(bp) > 0; bp = NEXT_BLKP(bp))
        if (!GET_ALLOC(bp) && (asize <= GET_SIZE(bp)))
            return bp;
    return NULL;
}

static void *find_last_block()
{
    void *bp;
    for (bp = heap_listp; GET_SIZE(bp) > 0; bp = NEXT_BLKP(bp))
        if (GET_SIZE(NEXT_BLKP(bp)) == 0)
            return bp;
    return NULL;
}

// void mm_check() {
//     void *bp;
//     void *lo = mem_heap_lo();
//     printf("\n");
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         printf("loc: %u / size: %u / alloc: %d\n", bp - lo, GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)));
//     }
//     printf("\n");
// }

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(bp);

    if ((csize - asize) >= DSIZE)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(2 * WSIZE, 0));
    PUT(heap_listp + (2 * WSIZE), 0);
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    asize = DSIZE * ((size + (3 * WSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    void *end = find_last_block();
    extendsize = end == NULL || GET_ALLOC(end) ? asize : asize - GET_SIZE(end);

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);

    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (ptr == NULL)
        return;

    size_t size = GET_SIZE(ptr);

    PUT(HDRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;

    size_t old_size = GET_SIZE(ptr) - WSIZE;
    size_t asize = GET_SIZE(ptr) + GET_SIZE(NEXT_BLKP(ptr));

    if (ptr == NULL)
    {
        return mm_malloc(size);
    }

    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    if (size > old_size)
    {
        newptr = mm_malloc(size);
        if (newptr == NULL)
            return NULL;
        memcpy(newptr, ptr, old_size);
        mm_free(ptr);
        return newptr;
    }
    else
    {
        place(ptr, old_size);
        coalesce(NEXT_BLKP(ptr));
        return ptr;
    }

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    memcpy(newptr, ptr, old_size - WSIZE);
    mm_free(ptr);
    return newptr;
}