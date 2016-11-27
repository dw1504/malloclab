
/*
 * 
 * In our approach, a block is allocated from a segregated free list. We have
 * defined functions that provides the address of a free block's previous and 
 * next block, allowing us to traverse the linked lists to search for the 
 * right-sized block that we need. A block includes the payload, header and 
 * footer; in addition, given a block pointer, the address of the previous and 
 * next block can also be computed.Blocks are coalesced in cases such as extending 
 * the heap or freeing a block. Realloc is implemented using mm_malloc and
 * mm_free; additionally, we included an initial check for a case that would
 * allow for reallocating in place (this way, we do not always have to copy the
 * information from the original block to a new block).
 *
 */


#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"


team_t team = {
    /* Team name */
    "BYEBYE MALLOC HA HA",
    /* First member's full name */
    "Christine Zheng",
    /* First member's email address */
    "cz786@nyu.edu",
    /* Second member's full name (leave blank if none) */
    "Dongning Wang",
    /* Second member's email address (leave blank if none) */
    "dw1504@nyu.edu"
};


/** Reference: used code provided in the 
textbook (Chapter 9.9: Dynamic Memory Allocation) **/

// Basic constants and Macros
#define WSIZE 8 		// word and header/footer size (bytes)
#define DSIZE 16 		// double word size (bytes)
#define CHUNKSIZE (1<<12)	// extend heap by this amount (bytes)

#define LISTLIMIT 20

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// Read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// Given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

// Address of free block's prev and next on the segregated list
#define NEXT(bp) (*(void **)(bp))
#define PREV(bp) (*(void **)(((char *)(bp) + WSIZE)))

//Address of segregated free list
#define GET_FREELIST(free_list, i) (*(void **)(free_list + (i*DSIZE)))

//Global Variable: pointer to segregated free list
/* Reference: We learned how to access a segregated free list using
only a global pointer. https://github.com/ohyeslk/CMU15213-
MallocLab-score93/blob/master/mm_submission2_93.c#L1505 */
static char *free_list = 0;


// Functions
static void *extend_heap(size_t size);
static void *coalesce(void *bp);
static void *place(void *bp, size_t asize);
static void insert(void *bp, size_t size);
static void detach(void *bp);
void mm_checkheap(int verbose);


/*Extends the heap with a new free block*/ 
void *extend_heap(size_t words)
{
	void *bp;
	size_t size;
	//Maintain alignment
	size = ALIGN(words);
	if ((bp = mem_sbrk(size)) == (void *)-1){
		return NULL;
	}
	// Initialize free block header/footer and the epilogue footer 
	PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
	insert(bp, size);
	return coalesce(bp);
}


/*insert the node to the free list*/
void insert(void *bp, size_t size) {
	int list = 0; 
	void *search_bp = bp;
	void *insert_bp = NULL;

	// find the correct size in the segregated list 
	while ((list < LISTLIMIT - 1) && (size > 1)) {
		size /= 2;
		list++;
	}

	// find the correct location in the linked list 
	search_bp = GET_FREELIST(free_list,list);//free_lists[list];
	while ((search_bp != NULL) && (size > GET_SIZE(HDRP(search_bp)))) {
		insert_bp = search_bp;
		search_bp = NEXT(search_bp);
	}

	// insert the node to its position 
	if (search_bp != NULL) { 
		//if not the biggest nor the smallest
		if (insert_bp != NULL) { 
			NEXT(bp) = search_bp;
			PREV(search_bp) =  bp;
			PREV(bp) = insert_bp;
			NEXT(insert_bp) = bp;
		} 
		//the smallest node
		else { 
			NEXT(bp) = search_bp;
			PREV(search_bp) = bp;
			PREV(bp) = NULL;
			GET_FREELIST(free_list,list) = bp;
		}
	} 
	else {
		//last node
		if (insert_bp != NULL) {
			NEXT(bp) = NULL;
			PREV(bp) = insert_bp;
			NEXT(insert_bp) = bp;
		} 
		//the only node in the list
		else {
			NEXT(bp) = NULL;
			PREV(bp) = NULL;
			GET_FREELIST(free_list,list) = bp;
		}
	}
	return;
}


/*detach the node from the free list*/
void detach(void *bp) {
	int list = 0;
	size_t size = GET_SIZE(HDRP(bp));

	//find the correct size in the segregated list
	while ((list < LISTLIMIT - 1) && (size > 1)) {
		size /= 2;
		list++;
	}

	//find the correct position in the linked list
	if (NEXT(bp) != NULL) {
		//if not the smallest or the largest number
		if (PREV(bp) != NULL) { 
			PREV(NEXT(bp)) = PREV(bp);
			NEXT(PREV(bp)) = NEXT(bp);
		} 
		//the smallest node
		else {
			PREV(NEXT(bp)) = NULL;
			GET_FREELIST(free_list,list) = NEXT(bp);
		}
	} 
	else {
		//the last node
		if (PREV(bp) != NULL) {
			NEXT(PREV(bp)) = NULL;
		} 
		//the only node
		else {
			GET_FREELIST(free_list,list) = NULL;
		}		
	}
	return;
}


/*merge with any adjacent free blocks*/
void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	//Case 1
	if (prev_alloc && next_alloc) { 
		return bp;
	}
	//Case 2
	else if (prev_alloc && !next_alloc) {
		detach(bp);
		detach(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}
	//Case 3
	else if (!prev_alloc && next_alloc) {
		detach(bp);
		detach(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);	
	} 
	//Case 4
	else {
		detach(bp);
		detach(PREV_BLKP(bp));
		detach(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}		
	insert(bp, size);
	return bp;
}


/*place the block to its position*/
void *place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));
	size_t remainder = csize - asize;
	detach(bp);

	//if block is too small to split
	if (remainder <= DSIZE * 2) {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
	//block big enough to split
	else if (asize >= 112) {
		PUT(HDRP(bp), PACK(remainder, 0));
		PUT(FTRP(bp), PACK(remainder, 0));
		PUT(HDRP(NEXT_BLKP(bp)), PACK(asize, 1));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(asize, 1));
		insert(bp, remainder);
		return NEXT_BLKP(bp);
	}
	else {
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		PUT(HDRP(NEXT_BLKP(bp)), PACK(remainder, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(remainder, 0));
		insert(NEXT_BLKP(bp), remainder);
	}
	return bp;
}


/*
* Creates a heap with an initial free block 
* Return -1 if there was a problem initializing, 0 otherwise.
*/
int mm_init(void)
{
	char *heap_listp; 
	free_list = NULL;
	
	//allocate memory for the segregated free list and initialize it
	free_list = mem_sbrk(LISTLIMIT * DSIZE);
	for (int i = 0; i < LISTLIMIT ; ++i){
		GET_FREELIST(free_list,i) = NULL;
	}
	
	//Create the initial empty heap
	if ((long)(heap_listp = mem_sbrk(4 * WSIZE)) == -1){
		return -1;
	}
	PUT(heap_listp, 0); 					/* Alignment padding */
        PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); 		/* Prologue header */
        PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); 		/* Prologue footer */
        PUT(heap_listp + (4 * WSIZE), PACK(0, 1)); 		/* Epilogue header */	


	//extend the empty heap with a free block of CHUNCKSIZE bytes
	if(extend_heap(CHUNKSIZE) == NULL){
		return -1;
	}
	return 0;
}


/*
allocates a block from the segregated free list
if no big enough free blocks are found, extend heap
*/
void *mm_malloc(size_t size)
{
	//mm_checkheap(1);
	size_t asize; 		/* Adjusted block size */
	size_t extendsize; 	/* Amount to extend heap if no fit */
	void *bp = NULL; 

	// Ignore spurious requests
	if (size == 0)
		return NULL;
	// Adjust block size to include overhead and alignment reqs.
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = ALIGN(size+DSIZE);


	int list = 0;
	size_t searchsize = asize;
	// Find correct location in the segregated free list
	while (list < LISTLIMIT) {
                if ((list == LISTLIMIT - 1) || ((searchsize <= 1) && (GET_FREELIST(free_list,list) != NULL))) {
			bp = GET_FREELIST(free_list,list);
			// Skip blocks that are too small
			while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp))))){
				bp = NEXT(bp);
			}
			if (bp != NULL){
				break;
			}
		}
		searchsize /= 2;
		list++;
	}

	// If no fit found, get more memory space and place the block
	if (bp == NULL) {
		extendsize = MAX(asize, CHUNKSIZE);
		if ((bp = extend_heap(extendsize)) == NULL)
			return NULL;
	}
	bp = place(bp, asize);
	return bp;
}


/*frees the block and inserts it to the segregated free list*/
void mm_free(void *bp)
{
	size_t size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	insert(bp, size);
	coalesce(bp);
}


/*
try reallocating in place to maximize efficiency
if not possible, find a new location and copy over the content of the old block
*/
void *mm_realloc(void *bp, size_t size)
{
	void *new_bp = bp; 		//pointer to the reallocated block
	size_t new_size = size;		//reallocated size
	int remainder;
	int extendsize;

	//ignore spurious requests
	if (size == 0){
		return NULL;
	}
	//adjust block size to include overhead and alignment reqs.
	if (new_size <= DSIZE) {
		new_size = 2 * DSIZE;
	} 
	else {
		new_size = ALIGN(size+DSIZE);
	}
	//check if possible to merge with the next block
	if (!GET_ALLOC(HDRP(NEXT_BLKP(bp))) || !GET_SIZE(HDRP(NEXT_BLKP(bp)))) {
		//check if bp and its next block combined is big enough for reallocation
		remainder = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(NEXT_BLKP(bp))) - new_size;
		
		//if block is not big enough
		if (remainder < 0) {
			extendsize = MAX(-remainder, CHUNKSIZE);
			if (extend_heap(extendsize) == NULL){
				return NULL;
			}
			remainder += extendsize;
		}
		//merge
		detach(NEXT_BLKP(bp));
		PUT(HDRP(bp), PACK(new_size + remainder, 1));
                PUT(FTRP(bp), PACK(new_size + remainder, 1));
		
	} 
	//if new block is used, copy over info from old block
	else {
		new_bp = mm_malloc(new_size - DSIZE);
		memcpy(new_bp, bp, MIN(size, new_size));
		mm_free(bp);
	}
	return new_bp;
}


/* check for errors */
void mm_checkheap(int verbose){
	//check if all blocks in segregated free list are free
	for (int i = 0; i < LISTLIMIT-1; i++){
		void* bp = GET_FREELIST(free_list,i);
		while (bp != NULL){
			if(GET_ALLOC(bp) == 1){
				printf("You have an allocated block in the free list");
			}
			bp = NEXT(bp);
		}
	}
}

