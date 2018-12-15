/*
 * This solution uses an implicit free list and implements several find-fit policies
 * for the free list. In addition, this solution has been optimised such that the footer
 * allocated blocks has been removed. 
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Have mercy pls",
    /* First member's full name */
    "Búgvi Benjamin Magnussen (group70)",
    /* First member's email address */
    "buma@itu.dk",
    /* Second member's full name (leave blank if none) */
    "Nikolaj Bläser (group89)",
    /* Second member's email address (leave blank if none) */
    "nibl@itu.dk"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* size_t is the size of an unsigned integer.
 * This can vary depending on which system you are using. */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (4096 bytes) */ 

/* Macros */

/* Dereferences the pointer and casts it to an unsigned int.*/
#define GET(p) (*(unsigned int *) p)  

/* Read and write a word at address p */
#define PUT(p, val) (*(unsigned int*)(p) = (val))

/* Returns the length of the block at which the pointer is pointing at. */
#define GET_SIZE(p) (GET(p) & ~0x7)

/* Returns whether the previous block is allocated or not. (used for footer optimization) */
#define ISPREV_ALLOC(p) ((GET(p)>>1) & 0x1) 

/* Checks if pointer is allocated */
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Creates a header which includes information of the length of the block
 * and whether the block is allocated or not. */
#define PACK(length, isPrevAllocated, isAllocated) ((length) | (isPrevAllocated << 1)| (isAllocated))

/*Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*Given block ptr bp, compute address of next and previous blocks*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define MAX(x, y) ((x) > (y)? (x) : (y))

/*The following macros are used to implement different methods to manage and represent a freelist.*/

/* Change the following line to BESTFIT/FIRSTFIT/NEXTFIT in order to change the approach of choosing 
 * free blocks when allocating. */
#define NEXTFIT

/* Used to enable/disable the heap checker. */
//#define CHECK

/* Only works when "CHECK" is defined. Prints out each block in the heap for every time
 * malloc, realloc, free and init is called. */
//#define PRINTCHECK


/* Forward declaration */
static void *extend_heap(size_t words);

static void *coalesce(void *bp);

static void *find_fit(size_t newsize);

static void place(void *bp, size_t newsize);

#ifdef CHECK
static int mm_check(void);
#endif

/* Private global variables */

static char *heap_listp = 0;

/* This pointer is used to store the location at which the next call to allocate
 * will start to look for a fitting free block. The pointer points at the block that comes
 * after the most recent allocated free block. (NEXTFIT approach)*/
#ifdef NEXTFIT
static char *next_fitp = 0; 
#endif

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
#ifdef CHECK
	printf("init \n");
#endif
	/*Create the heap and return -1 if an error occured. (Not enough memory available) */
	if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
		return -1;
	PUT(heap_listp,0); /* Alignment padding */
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1, 1)); /* Prologue header */
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1, 1)); /* Prologue footer */
	PUT(heap_listp + (3*WSIZE), PACK(0, 1, 1));     /* Epilogue header */
	/* Set heap_listp to point at prologue footer. */
	heap_listp += (2*WSIZE);
    	
	/* Extend the heap by 4096 bytes, return -1 if error occurs. */
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
		return -1;
#ifdef CHECK
	mm_check();
#endif
	return 0;

}

/* 
 * Search the free list for a block that can be used to store 
 * the size given as a parameter. If no such block exists, extend the heap to
 * create a free block that is large enough.
 * Always allocate a block whose size is a multiple of the alignment.
 */

void *mm_malloc(size_t size)
{
#ifdef CHECK
	mm_check();
	printf("malloc size: %i \n", size);
#endif
	if(heap_listp == 0){ 
		mm_init();
	}	

	size_t newsize;
        size_t extendsize;
	char *bp;
	
	
	if (size == 0) {
		return NULL;
	}
	
	/* Make sure that the size given as parameter is 8 byte aligned. And add overhead. */
	
	if(size <= WSIZE){
		newsize = DSIZE;
	}
	else{
		newsize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE);
	}

	/* Search the free list for a fit */
	if ((bp = find_fit(newsize)) != NULL) {
		place(bp, newsize);
		return bp;
	}


	/*No fit found. Get more memory and place the block 
	 * The size with which the heap is extended is always the 
	 * size given as parameter. This decision has been made because
	 * it gives the best performance in regards to the test cases. */
	//extendsize = MAX(newsize,CHUNKSIZE);
	extendsize = newsize;
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
		return NULL;
	}
	place(bp, newsize);
	return bp;
}

/*
 * Free the block at which the pointer given as a parameter points at.
 * This is done by setting the header and footer to not allocated and afterwards
 * checking if neighbouring blocks are free blocks as well. If this is the case they
 * are merged into one free block. 
 */

void mm_free(void *ptr)
{
#ifdef CHECK
	mm_check();
	printf("free called with: %p \n", ptr);
#endif
	size_t size = GET_SIZE(HDRP(ptr));
	PUT(HDRP(ptr), PACK(size, ISPREV_ALLOC(HDRP(ptr)), 0));
	PUT(FTRP(ptr), PACK(size, ISPREV_ALLOC(HDRP(ptr)), 0));		
	coalesce(ptr);	
}

/*
 * Realloc reallocates a previously allocated memory block. 
 */
void *mm_realloc(void *ptr, size_t newSize)
{
#ifdef CHECK
	mm_check();
	printf("realloc size: %i ptr: %p \n", newSize, ptr);
#endif
	void *oldptr = ptr;
	size_t oldSize;
	
	if(oldptr == NULL){
		return mm_malloc(newSize);
	}
	
	/* Check if ptr is within the heap */
	if(!(oldptr > mem_heap_lo() && oldptr < mem_heap_hi())){
		return NULL;	
	}	
	/* Check if given size is 0, in that case free the block at which
	 * the pointer given as parameter is pointing at. */
	if(newSize == 0){
		mm_free(oldptr);
		return NULL;
	}
	
	/*Size of the block the pointer given as parameter is pointing at. */
	oldSize = GET_SIZE(HDRP(oldptr)) - WSIZE;
	/*If old size is equal to the size given as parameter, then there is nothing to be
	 * done. */
	if(oldSize == newSize){
		return oldptr;
	}

	/*If oldsize is less than size, a new block for the new size is allocated, and the
	 * content of the old block is copied to the new block. */
	else if(oldSize < newSize){
		ptr = mm_malloc(newSize);
		/* If malloc fails, return the old pointer and dont reallocate. */
		if(ptr == NULL){
			return oldptr;
		}
		/* Copy the payload of the old block to the payload of the new block
		 * and free the old block. */
		memcpy(ptr,oldptr, oldSize);
		mm_free(oldptr);

		return ptr;
	}
	else{ // oldSize > newSize
		/* Call place which if possible, splits the original block into 
		 * an allocated block with the new size, and a free block. */
		place(oldptr, newSize+WSIZE);
		
		if(!(GET_ALLOC(HDRP(NEXT_BLKP(oldptr))))){
			coalesce(NEXT_BLKP(oldptr));
		}


		return oldptr;	
	}
}

/* Extend the heap by the size given as parameter and return a pointer that
 * points to the start of the new memory. */
static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;
	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, ISPREV_ALLOC(HDRP(bp)), 0)); /* Free block header */
	PUT(FTRP(bp), PACK(size, ISPREV_ALLOC(HDRP(bp)), 0)); /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 0, 1));	/* New epilogue header */
	return coalesce(bp);
}


/* Coalesce is responsible for merging free blocks. This method is similar to the one
 * defined in the book. The only difference is that this method uses the ISPREV_ALLOC macro
 * to determine whether a previous block is allocated or not. (done for footer optimization) */
static void *coalesce(void *bp)
{
	size_t prev_alloc = ISPREV_ALLOC(HDRP(bp));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	if (prev_alloc && next_alloc) {		/* Case 1 */ 	
		PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 0, 1));	
		return bp;
	}

	else if (prev_alloc && !next_alloc) {	/* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 1, 0));
		PUT(FTRP(bp), PACK(size, 1, 0));
	}
	
	else if (!prev_alloc && next_alloc) {	/* Case 3 */	
		PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 0, 1));	
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 1, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1, 0));
		bp = PREV_BLKP(bp);
	}

	else {					/* Case 4 */	
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1, 0));
		bp = PREV_BLKP(bp);
	}

	/* if the next fit pointer pointed to a block that has been merged, 
	 * it is set to now point at the start of the free block. */
#ifdef NEXTFIT
	if(((void *)next_fitp > bp) && (next_fitp < NEXT_BLKP(bp))){
		next_fitp = bp;
	}
#endif
	return bp;
}


/* Find_fit is responsible for traversing the heap (implicit freelist) and finding
 * an unallocated block that meets the size requirement which is given as a parameter.
 * The method implements several different policies, which can be toggled at the start of the file.*/
static void *find_fit(size_t size){
	void *bp;
/* Traverse the heap until a free block that meets the size requirement is found. */
#ifdef FIRSTFIT
	for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
		char *header = HDRP(bp);
		if((!GET_ALLOC(header)) && (size <= GET_SIZE(header))){
			return bp;
		}
	}
#endif
/* Traverse the heap by starting at the next fit pointer. (global variable)
 * If the end of the heap is reached, continue from the beginning and stop as soon
 * as the next fit pointer is reached again. */
#ifdef NEXTFIT 
	if(next_fitp == 0){
		next_fitp = heap_listp;
	}
	
	for(bp = next_fitp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
		char *header = HDRP(bp);
		if((!GET_ALLOC(header)) && (size <= GET_SIZE(header))){
			return bp;
		}	
	}
	
	for(bp = heap_listp; bp != next_fitp; bp = NEXT_BLKP(bp)){
	       char *header = HDRP(bp);
       	       if((!GET_ALLOC(header)) && (size <= GET_SIZE(header))){
	       		return bp;
	       }	       
	}
#endif
/* Traverses the entire freelist and finds the best fit. 
 * Best fit here is defined as having the minimal difference between
 * the size given as parameter and the size of the free block. */
#ifdef BESTFIT
	void *bestptr = 0;
	size_t mindiff = -1;	
	for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
		char *header = HDRP(bp);
		if(!GET_ALLOC(header) && (size <= GET_SIZE(header))){
			size_t new_mindiff = GET_SIZE(header) - size;
			if(new_mindiff == 0){
				return bp;
			}
			if(bestptr == 0){
				bestptr = bp;
				mindiff = new_mindiff;
			}else{
				if(new_mindiff < mindiff){
					bestptr = bp;
					mindiff = new_mindiff;
				}
			}	
		}
	}
	if(bestptr != 0){
		return bestptr;
	}
#endif
	return NULL;
}


/* Place is responsible for splitting a free block into an allocated block
 * consisting of the size given as parameter and a free block consisting of the rest
 * of the original free block. If the rest is not big enough, the whole free block is allocated.*/
static void place(void *bp, size_t size){
	size_t length = GET_SIZE(HDRP(bp));
	size_t rest = length - size;
	if((rest) < (4*WSIZE)){
		PUT(HDRP(bp), PACK(length, ISPREV_ALLOC(HDRP(bp)), 1));
		PUT(HDRP(NEXT_BLKP(bp)), 
				PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 
					1, GET_ALLOC(HDRP(NEXT_BLKP(bp)))));

/* Next fit is set here, since place is called with a free block allocated by find_fit.
 * The next fit pointer now has to be changed to point at the next free block. */
#ifdef NEXTFIT
		if(!GET_SIZE(HDRP(NEXT_BLKP(bp)))){
			next_fitp = heap_listp;	
		}
		else{
			next_fitp = NEXT_BLKP(bp);
		}
#endif	
	}else{
		PUT(HDRP(bp), PACK(size, ISPREV_ALLOC(HDRP(bp)), 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(rest, 1, 0));
		PUT(FTRP(bp), PACK(rest, 1, 0));
#ifdef NEXTFIT
		next_fitp = bp;
#endif

	}
}


#ifdef CHECK
/* Returns whether the pointer given as parameter is in heap or not. */
static int inHeap(void *bp){
	if(!(bp > mem_heap_lo() && bp < mem_heap_hi())){
		return 0;
	}
	else return 1;
}

/* Prints all information associated with the block pointed at 
 * by the pointer given as parameter. */
static void printBlock(void *bp){
	printf("Header size: %i \n", GET_SIZE(HDRP(bp)));
	printf("Header alloc: %i \n", GET_ALLOC(HDRP(bp)));
	printf("Header prevalloc: %i \n", ISPREV_ALLOC(HDRP(bp)));
	printf("Footer size: %i \n", GET_SIZE(FTRP(bp)));
	printf("Footer alloc: %i \n", GET_ALLOC(FTRP(bp)));
	printf("Footer prevalloc: %i \n", ISPREV_ALLOC(FTRP(bp)));
	printf("------------------\n");
}


/* Checks if the block given as parameter is 8 byte aligned and the 
 * footer and header are equal. */
static int blockCheck(void *bp){
	int error = 0;
	if(((size_t) bp % 8)){
		printf("payload not aligned \n");
		error = 1;
	}
	/* Only compare header with footer if the block is free, there is no footer otherwise */
	if((!GET_ALLOC(HDRP(bp))) && GET(HDRP(bp)) != GET(FTRP(bp))){
		printf("footer and header not equal \n");
		printBlock(bp);
		printBlock(NEXT_BLKP(bp));
		error = 1;
	}

	return error;
}	

/* mm_check is a debugging method that can be toggled at the start of the file. */
static int mm_check(void){
	int error = 0;

	if(GET_SIZE(HDRP(heap_listp)) != DSIZE){
		printf("Broken prologue size \n");
		error = 1;

	}
	if(!(GET_ALLOC(HDRP(heap_listp)))){
		printf("broken prologue allocate \n");
		error = 1;
	}
	
	if(!(ISPREV_ALLOC(HDRP(heap_listp)))){
		printf("broken prologue prev allocate \n");
		error = 1;
	}

	/* traverse the heap, check each block for alignment, header/footer comparison and print the block. */
	void *bp;
	for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
#ifdef PRINTCHECK
		printBlock(bp);
#endif
		if(!inHeap(bp)){
			printf("Traversal failed \n");
			error = 1;
			break;
		}
		error = blockCheck(bp);
	}
	/* Print the epilogue header */
	printf("epilogue size: %i \n", GET_SIZE(HDRP(bp)));
	printf("epilogue alloc: %i \n", GET_ALLOC(HDRP(bp)));
	printf("epilogue prevalloc: %i \n", ISPREV_ALLOC(HDRP(bp)));

	/* Check epilogue header */
	if(!GET_ALLOC(HDRP(bp))){
		printf("Broken epilogue header \n");
		error = 1;
	}
	if((GET_SIZE(HDRP(bp))) != 0){
		printf("broken epilogue size \n");
		error = 1;
	}
	printf("\n\n");
	if(error == 1) exit(1);

	return error; 
}
#endif
