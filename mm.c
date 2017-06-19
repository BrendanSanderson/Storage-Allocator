/*
 * mm.c
 * This is the only file you should modify.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
//#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif
/*
 * If NEXT_FIT defined use next fit search, else use first fit search 
 */
//#define NEXT_FIT

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */
#define DSIZE       8       /* doubleword size (bytes) */
#define QSIZE       16       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    16      /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
/* NB: this code calls a 32-bit quantity a word */
#define GET(p)       (*(unsigned int *)(p))
#define GETL(p)      (*(unsigned long *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

#define GETA(bp)      ((char *)*(unsigned long*)bp) 
#define PUTA(p, val)    (*(unsigned long *)(p) = (unsigned long)(val))



/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
#define NEXT_FRP(bp)   ((char *)(bp) + DSIZE)
#define PREV_FRP(bp)   ((char *)(bp))

#define PUTAN(p, val) (*(unsigned long *)(NEXT_FRP(p)) = (unsigned long)(val))
#define PUTAP(p, val) (*(unsigned long *)(PREV_FRP(p)) = (unsigned long)(val))


/* $end mallocmacros */

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - DSIZE))

#define MINIMUM 24

/* Global variables */
static char *heap_listp = 0;  /* pointer to first block */  
static char *rover;       /* next fit rover */

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);
static void removefblock(void *bp);
static void addfblock(void *bp);

/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void)
{
    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(8*WSIZE)) == NULL)
        return -1;
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD+DSIZE, 1));  /* prologue header */
    PUTAP(heap_listp+DSIZE, 0);  
    PUTAN(heap_listp+DSIZE, 0);  
    PUT(heap_listp+QSIZE+DSIZE, PACK(OVERHEAD+DSIZE, 1));  /* prologue footer */
    PUT(heap_listp+QSIZE+DSIZE+WSIZE, PACK(0, 1));   /* epilogue header */
    heap_listp += DSIZE;
    rover = heap_listp;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;

}
/* $end mminit */

/*
 * malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size)
{
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;
    if (heap_listp == 0){
      mm_init();
    }
    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
      asize = DSIZE + OVERHEAD;
    else
      asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/* $end mmmalloc */

/* 
 * free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    if(bp == 0) return;
    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
      mm_init();
    }
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
    //checkheap(0);
}
/* $end mmfree */

/* Not implemented. For consistency with 15-213 malloc driver */
void *mm_realloc(void *ptr, size_t size)
{
    dbg_printf("Calling mm_relloc........");
    size_t oldsize;
    void *newptr;
    size_t asize;
    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }
    
    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }
    oldsize = GET_SIZE(HDRP(ptr));
    if (size <= DSIZE)
      asize = DSIZE + OVERHEAD;
    else
      asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);

    if ((asize <= oldsize) && (oldsize - size <= MINIMUM))
        return ptr;

    if(asize + MINIMUM <= oldsize)
    {
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        void *bp = NEXT_BLKP(ptr);
        PUT(HDRP(bp), PACK(oldsize-asize, 1));
        PUT(FTRP(bp), PACK(oldsize-asize, 1));
        mm_free(bp);
        return ptr;
    }

    newptr = mm_malloc(size);
    
    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);
    
    /* Free the old block. */
    mm_free(ptr);
    
    return newptr;
}

/* 
 * checkheap - Minimal check of the heap for consistency 
 */
void mm_checkheap(int verbose)
{
  char *bp = heap_listp;

  if (verbose)
    printf("Heap (%p):\n", heap_listp);

  if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
    printf("Bad prologue header\n");
  checkblock(heap_listp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (verbose) 
      printblock(bp);
    checkblock(bp);
  }

  if (verbose)
    printblock(bp);
  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
    printf("Bad epilogue header\n");
}

static void removefblock(void *bp)
{
    char *nextfblock = GETA(NEXT_FRP(bp));
    char *prevfblock = GETA(PREV_FRP(bp));
    if (rover == (char *) bp)
      rover = nextfblock;
    PUTAN(prevfblock, nextfblock);
    if (nextfblock != NULL) {
        PUTAP(nextfblock, prevfblock);
    }
}

static void addfblock(void *bp)
{

    PUTAN(bp, GETL(NEXT_FRP(heap_listp)));
    PUTAP(bp, heap_listp);
    
    char *nextfblock = GETA(NEXT_FRP(heap_listp));
    PUTAN(heap_listp, bp);
    if (nextfblock != NULL) {
        PUTAP(nextfblock, bp);
    }
}


/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words)
{
    void *bp;
    size_t size;
    void *return_ptr;
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) < 0)
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */
    
    /* Coalesce if the previous block was free */
    return_ptr = coalesce(bp);
    //mm_checkheap(0);
    return return_ptr;
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= MINIMUM) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        removefblock(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        addfblock(bp);
        
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        removefblock(bp);
    }
}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize)
{
  /* next fit search */
  void *oldrover = rover;
  void *bp;
  /* search from the rover to the end of list */
  for (bp = (void *)oldrover; bp > 0; bp = GETA(NEXT_FRP(bp)))
  {

    if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
    {
      rover = (char *) bp;
      return bp;
    }
  }
  /* search from start of list to old rover */
  for (bp = heap_listp; bp >0 && bp != oldrover; bp = GETA(NEXT_FRP(bp)))
  {
    if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
    {
      rover = (char *) bp;
      return bp;
    }
  }
  return NULL;  /* no fit found */
}
/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    if (prev_alloc && next_alloc) {            /* Case 1 */
        addfblock(bp); 
        return (bp);
    }
    
    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        removefblock(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
        addfblock(bp);
    }
    
    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        removefblock(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        addfblock(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);
    }
    
    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        removefblock(PREV_BLKP(bp));
        removefblock(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        addfblock(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);
    }
  if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp))) 
    rover = bp;
    return bp;
}

static void printblock(void *bp) 
{
  size_t hsize;//, halloc, fsize, falloc;

  hsize = GET_SIZE(HDRP(bp));
  //halloc = GET_ALLOC(HDRP(bp));  
  //fsize = GET_SIZE(FTRP(bp));
  //falloc = GET_ALLOC(FTRP(bp));  

  if (hsize == 0) {
    printf("%p: EOL\n", bp);
    return;
  }

  /*  printf("%p: header: [%p:%c] footer: [%p:%c]\n", bp, 
      hsize, (halloc ? 'a' : 'f'), 
      fsize, (falloc ? 'a' : 'f')); */
}

static void checkblock(void *bp) 
{
  if ((size_t)bp % 8)
    printf("Error: %p is not doubleword aligned\n", bp);
  if (GET(HDRP(bp)) != GET(FTRP(bp)))
    printf("Error: header does not match footer\n");
}

void *mm_calloc (size_t nmemb, size_t size)
{
  void *ptr;
  if (heap_listp == 0){
    mm_init();
  }

  ptr = mm_malloc(nmemb*size);
  bzero(ptr, nmemb*size);


  return ptr;
}
