/*
 * mm-seglist.c
 *
 * header와 footer에는 implicit list와 동일하게 block 크기와 할당 여부를 저장합니다.
 * free block의 경우 previous and next free block를 data로 갖으며 block 크기에 따라 doubly linked list를 구성합니다.
 * free_list는 segrated list로, 각 인덱스 n에는 2^n에서 2^(n+1) - 1 크기의 free block을 갖습니다.
 * 또한, 8-byte align이기 때문에 인덱스 0-2은 사용하지 않습니다.
 * malloc 할 때, heap 끝(마지막) block이 free block인지 판단하여 추가로 필요한 공간만 확장합니다.
 * realloc의 동작은 3가지 경우로 나눕니다.
 * 1. 크기가 줄어드는 경우, header와 footer만 수정하여 재할당 없이 크기를 수정합니다.
 * 2. 크기가 늘어나지만, 해당 블록 이후로 free block만 있거나 아무 block이 없는 경우, 필요한 공간을 확장한 후, 재할당 없이 크기를 수정합니다.
 * 3. 그 외는 메모리를 새로 할당하고, 데이터를 옮긴 후, 기존 메모리를 해제합니다.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNCKSIZE (1 << 12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define ASIZE(size) ((((size) + (DSIZE - 1)) & ~0x7) + DSIZE)

/* Pack a size and allocated bit intoa word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(size_t *)(p))
#define PUT(p, val) (*(size_t *)(p) = (size_t)(val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr pb, compute address of its header and footer */
#define HDRP(bp) ((void *)(bp) - WSIZE)
#define FTRP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((void *)(bp) + GET_SIZE(((void *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((void *)(bp) - GET_SIZE(((void *)(bp) - DSIZE)))

/* Given block ptr pb, compute address of its next and previous address */
#define NEXT(bp) ((void *)(bp))
#define PREV(bp) ((void *)(bp) + WSIZE)

/* Given block ptr bp, compute address of next and previous blocks in segrated lists */
#define NEXT_PTR(bp) (*(void **)NEXT(bp))
#define PREV_PTR(bp) (*(void **)PREV(bp))

// #define PUT_PTR(p, ptr) (*(size_t *)(p) = (size_t)(ptr))

#define CLASS_SIZE 20

// https://github.com/hehozo/Malloc-lab/blob/master/mm.c
// https://github.com/lsw8075/malloc-lab/blob/master/src/mm.c

static void *heap_listp;
static void *heap_end_ptr;
static void *free_list[CLASS_SIZE];

static void *coalesce(void *);
static void *extend_heap(size_t);
static void *find_fit(size_t);
static void place(void *, size_t);
static void push_block(void *);
static void pop_block(void *);

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    size_t alloc = GET_ALLOC(HDRP(bp));

    if (alloc)
        return NULL;
    else if (prev_alloc && next_alloc)
        return bp;
    else if (prev_alloc && !next_alloc)
    {
        pop_block(bp);
        pop_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        PUT(HDRP(NEXT_BLKP(bp)), 0);
        PUT(FTRP(bp), 0);
        PUT(HDRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        pop_block(bp);
        pop_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(bp), 0);
        bp = PREV_BLKP(bp);
        PUT(FTRP(bp), 0);
        PUT(HDRP(bp), PACK(size, 0));
    }
    else
    {
        pop_block(bp);
        pop_block(PREV_BLKP(bp));
        pop_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        PUT(HDRP(NEXT_BLKP(bp)), 0);
        PUT(FTRP(bp), 0);
        PUT(HDRP(bp), 0);
        bp = PREV_BLKP(bp);
        PUT(FTRP(bp), 0);
        PUT(HDRP(bp), PACK(size, 0));
        pop_block(bp);
    }
    push_block(bp);

    return bp;
}

static void *extend_heap(size_t size)
{
    void *bp;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    heap_end_ptr = NEXT_BLKP(bp);

    push_block(bp);

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void *find_fit(size_t asize)
{
    for (size_t i = 0, size = asize - 1; i < CLASS_SIZE; i++, size >>= 1)
    {
        if (i < CLASS_SIZE - 1 && size > 1)
            continue;

        void *tmp = NULL;
        for (void *bp = free_list[i]; bp != NULL; bp = NEXT_PTR(bp))
        {
            size_t free_size = GET_SIZE(HDRP(bp));
            if (free_size == asize)
                return bp;
            else if (free_size > asize)
                tmp = bp;
        }
        if (tmp != NULL)
            return tmp;
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    pop_block(bp);

    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        push_block(bp);
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void push_block(void *bp)
{
    size_t index = 0;
    for (size_t size = GET_SIZE(HDRP(bp)) - 1; size > 0 && index < CLASS_SIZE - 1; index++, size >>= 1)
        ;

    // LIFO strategy
    PUT(PREV(bp), &free_list[index]);
    PUT(NEXT(bp), free_list[index]);
    if (free_list[index])
        PUT(PREV(free_list[index]), bp);
    free_list[index] = bp;
}

static void pop_block(void *bp)
{
    if (GET_ALLOC(HDRP(bp)))
        return;
    void *prev = GET(PREV(bp));
    void *next = GET(NEXT(bp));
    if (prev != NULL)
        PUT(NEXT(PREV_PTR(bp)), next);
    if (next != NULL)
        PUT(PREV(NEXT_PTR(bp)), prev);
    PUT(PREV(bp), 0);
    PUT(NEXT(bp), 0);
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    for (size_t i = 0; i < CLASS_SIZE; i++)
        free_list[i] = NULL;

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += 2 * WSIZE;
    heap_end_ptr = NEXT_BLKP(heap_listp);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNCKSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    void *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    size_t asize = ASIZE(size);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    size_t last_block_size = GET_SIZE(FTRP(heap_end_ptr)) - DSIZE;
    size_t last_block_alloc = 1 - GET_ALLOC(FTRP(heap_end_ptr));
    size_t extendsize = asize - last_block_alloc * last_block_size;

    if ((bp = extend_heap(extendsize)) == NULL)
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

    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    push_block(ptr);
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t old_size = GET_SIZE(HDRP(ptr));
    size_t asize = ASIZE(size);
    size_t copy_size = size > old_size - DSIZE ? old_size - DSIZE : size;

    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    void *next_ptr = NEXT_BLKP(ptr);
    size_t last = GET_SIZE(HDRP(next_ptr)) == 0 ||
                  (GET_ALLOC(HDRP(next_ptr)) == 0 && GET_SIZE(HDRP(NEXT_BLKP(next_ptr))) == 0);
    size_t free = find_fit(asize) == NULL;

    if (old_size >= asize)
    {
        place(ptr, asize);
        coalesce(NEXT_BLKP(ptr));
        return ptr;
    }
    else if (free && last)
    {
        size_t extendsize = asize + DSIZE - GET_SIZE(HDRP(ptr)) - GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        if (extend_heap(extendsize) == NULL)
            return NULL;
        pop_block(NEXT_BLKP(ptr));

        size_t total_size = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(total_size, 1));
        PUT(FTRP(ptr), PACK(total_size, 1));
        place(ptr, asize);
        coalesce(NEXT_BLKP(ptr));

        return ptr;
    }
    else
    {
        void *newptr = mm_malloc(size);
        if (newptr == NULL)
            return NULL;

        memcpy(newptr, ptr, copy_size);
        mm_free(ptr);
        return newptr;
    }
}