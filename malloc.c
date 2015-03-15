	#include <stdio.h>
	#include <stdlib.h>
	#include <assert.h>
	#include <unistd.h>
	#include <string.h>
	#include "mm.h"
	#include "memlib.h"
	/*********************************************************
	* * NOTE TO STUDENTS: Before you do anything else, please
	* * provide your team information in the following struct.
	* ********************************************************/
	team_t team = {
	/* Team name */
		"GaoSquared",
	/* First member's full name */
		"Xunyi Gao",
	/* First member's email address */
		"xunyigao@wustl.edu",
	/* Second member's full name */
		"Adela Gao",
	/* Second member's email address */
		"gao.adela@wustl.edu"
	};
	
	
	/*Additional Macros defined*/
	#define WSIZE 4 //word size
	#define DSIZE 8 //double word size
	#define CHUNKSIZE (1<<12) //extend heap by this amount; initial heap size
	#define ALIGNMENT 8
	#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
	#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
	#define OVERHEAD 24 //The minimum block size
	#define MAX(x ,y) ((x) > (y) ? (x) : (y)) 
	#define PACK(size, alloc) ((size) | (alloc)) //Put the size and allocated byte into one word
	#define GET(p) (*(size_t *)(p)) //Read the word at address p
	#define PUT(p, value) (*(size_t *)(p) = (value)) //Write the word at address p
	#define GET_SIZE(p) (GET(p) & ~0x7) //get size from header/footer
	#define GET_ALLOC(p) (GET(p) & 0x1) //get allocate bit from header/footer
	#define HDRP(bp) ((void *)(bp) - WSIZE) //pointer to eader
	#define FTRP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //pointer to footer
	#define NEXT_BLKP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp))) //pointer to next block
	#define PREV_BLKP(bp) ((void *)(bp) - GET_SIZE(HDRP(bp) - WSIZE)) //pointer to previous block
	#define NEXT_FREEP(bp) (*(void **)(bp + DSIZE)) //pointer to next free block
	#define PREV_FREEP(bp) (*(void **)(bp)) //previous free blcok
	static char *heap_listp = 0; //bottom of heap
	static char *free_listp = 0; //point to the first free block in the explicit free list
	/*
	helper functions
	*/
	static void *extend_heap(size_t words);
	static void place(void *bp, size_t size);
	static void *find_fit(size_t size);
	static void *coalesce(void *bp);
	static void insert_at_front(void *bp);
	static void remove_block(void *bp);

	/*
	initialize heap
	*/
	int mm_init(void)
	{
	if((heap_listp = mem_sbrk(OVERHEAD+DSIZE)) == NULL){ //error: unable to get heap space
		return -1;
	}
	PUT(heap_listp, 0); //padding at start of heap
	PUT(heap_listp + WSIZE, PACK(OVERHEAD, 1)); //prologue header pointer 
	PUT(heap_listp + DSIZE, 0); //its previous pointer
	PUT(heap_listp + DSIZE + WSIZE, 0); //its next pointer
	PUT(heap_listp + OVERHEAD, PACK(OVERHEAD, 1)); //prologue footer pointer
	PUT(heap_listp + WSIZE + OVERHEAD, PACK(0, 1)); //epilogue footer
	free_listp = heap_listp + DSIZE; //free list pointer
	if(extend_heap(CHUNKSIZE) == NULL){ 
		return -1;
	}
	return 0;
	}
	/*
	allocate memory block according to payload and return pointer to that block
	*/

	void *mm_malloc(size_t size)
	{
	size_t adjustedsize; //actual allocated block size
	size_t extendedsize; //if we need to extend heap
	char *bp; //block pointer
	if(size <= 0){ //ignore weird request 
		return NULL;
	}
	adjustedsize = MAX(ALIGN(size) + DSIZE, OVERHEAD); //adjust to include overhead and alignment requirement
	if((bp = find_fit(adjustedsize))){ 
	place(bp, adjustedsize); //Place the block in the free list
	return bp;
	}
	extendedsize = MAX(adjustedsize, CHUNKSIZE); //no fit found; extend the heap
	if((bp = extend_heap(extendedsize)) == NULL){ 
	return NULL; 
	}
	place(bp, adjustedsize); //put block new heap
	return bp;
	}

	/*
	free memory block
	*/
	void mm_free(void *bp)
	{
	size_t size = GET_SIZE(HDRP(bp)); //Get the total block size
	PUT(HDRP(bp), PACK(size, 0)); //set allocation bit to 0
	PUT(FTRP(bp), PACK(size, 0)); 
	coalesce(bp); 
	}

	/*
	reallocate allocated bit
	*/
	void *mm_realloc(void *bp, size_t size)
	{
	size_t oldsize; 
	void *newbp; //point to the reallocated block
	size_t adjustedsize = MAX(ALIGN(size) + DSIZE, OVERHEAD); //for overhead and alignment
	if(size <= 0){ //means free block
	mm_free(bp); 
	return 0;
	}
	if(bp == NULL){ //no block existed
		return mm_malloc(size);
	}

	oldsize = GET_SIZE(HDRP(bp)); 
	if(oldsize == adjustedsize){ 
		return bp;
	}
	if(adjustedsize <= oldsize){ 
	size = adjustedsize;
	if(oldsize - size <= DSIZE){ //new payload is trivially big, no need to reallocate more space becasue alignment requirements have already given extra space
	return bp; 
	}
	//if we are putting a new block in memory and discarding old lock
	PUT(HDRP(bp), PACK(size, 1)); //update size
	PUT(FTRP(bp), PACK(size, 1)); 
	PUT(HDRP(NEXT_BLKP(bp)), PACK(oldsize - size, 1)); 
	mm_free(NEXT_BLKP(bp));
	return bp;
	}
	//If the block has to be expanded during reallocation
	newbp = mm_malloc(size); //Allocate a new block
	if(!newbp){ //If realloc fails the original block is left as it is
		return 0;
	}
	if(size < oldsize){
		oldsize = size;
	}
	memcpy(newbp, bp, oldsize); 
	mm_free(bp); 
	return newbp;
	}

	/*
	ask for more heap space
	*/
static void* extend_heap(size_t words){
		char *bp;
		size_t size;
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; 
	if(size < 2*DSIZE){
		size = 2*DSIZE;
	}
	if((int)(bp = mem_sbrk(size)) == -1){ 
		return NULL;
	}
	PUT(HDRP(bp), PACK(size, 0)); 
	PUT(FTRP(bp), PACK(size, 0)); 
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); 
	return coalesce(bp); 
}
	/*
	coalesce adjacent blocks
	*/
static void *coalesce(void *bp){
	size_t previous_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp; 
	size_t next__alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); 
	size_t size = GET_SIZE(HDRP(bp)); 

	//Case 1: next block is free
	if(previous_alloc && !next__alloc){ 
	size += GET_SIZE(HDRP(NEXT_BLKP(bp))); 
	remove_block(NEXT_BLKP(bp)); 
	PUT(HDRP(bp), PACK(size, 0)); 
	PUT(FTRP(bp), PACK(size, 0)); 
	}
	//Case 2: previous block is free
	else if(!previous_alloc && next__alloc){ 
	size += GET_SIZE(HDRP(PREV_BLKP(bp))); 
	bp = PREV_BLKP(bp); 
	remove_block(bp); 
	PUT(HDRP(bp), PACK(size, 0)); 
	PUT(FTRP(bp), PACK(size, 0)); 
	}
	//case 3: both previous and next block is free
	else if(!previous_alloc && !next__alloc){ //Case 3: The blocks to the either side of the current block are free
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp))); 
	remove_block(PREV_BLKP(bp)); 
	remove_block(NEXT_BLKP(bp)); 
	bp = PREV_BLKP(bp); 
	PUT(HDRP(bp), PACK(size, 0)); 
	PUT(FTRP(bp), PACK(size, 0)); 
	}
	insert_at_front(bp); 
	//case 4: if both are not free, do nothing
	return bp;
}

	/*
	insert free block at root of free list
	*/
static void insert_at_front(void *bp){
	NEXT_FREEP(bp) = free_listp; 
	PREV_FREEP(free_listp) = bp; 
	PREV_FREEP(bp) = NULL; 
	free_listp = bp; 
}
	/*
	remove allocated block from free list
	*/
static void remove_block(void *bp){
	if(PREV_FREEP(bp)){ 
	NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp); //next pointer of the previous block points to next block
	}
	else{ 
	free_listp = NEXT_FREEP(bp); 
	}
	PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp); //revious block's next pointer points to the previous block
}
	/*
	try approximate best fit, if not then fist fit
	*/
static void *find_fit(size_t size){//new basepointer parameter
		void *bp;
//implement approximate best fit for threschold in the following
	for(bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEP(bp)){ //Traverse the entire free list
	    if(( (GET_SIZE(HDRP(bp)))-size)<= 4*CHUNKSIZE){ //If the size is within this threshold (this threshold yields highest utility so far)
	return bp;
		}
	}
//implement first fit (because next fit yields the same result here)
	for(bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEP(bp)){ 
	if(size <= GET_SIZE(HDRP(bp))){ 
		return bp; 
	}

	}
	return NULL; 
	}

	/*
	place the block pointer (bp) of the newly freed block at the start of free list
	*/

	static void place(void *bp, size_t size){

	size_t totalsize = GET_SIZE(HDRP(bp)); 

	if((totalsize - size) >= OVERHEAD){ //If the difference between the total size and requested size is more than overhead, split the block

	PUT(HDRP(bp), PACK(size, 1)); 
	PUT(FTRP(bp), PACK(size, 1)); 
	remove_block(bp);
	bp = NEXT_BLKP(bp); 
	PUT(HDRP(bp), PACK(totalsize - size, 0)); 
	PUT(FTRP(bp), PACK(totalsize - size, 0)); 
	coalesce(bp); 
	}

	else{ //If not enough space for a free block then no splitting
	PUT(HDRP(bp), PACK(totalsize, 1)); 
	PUT(FTRP(bp), PACK(totalsize, 1)); 
	remove_block(bp);
	}
	}