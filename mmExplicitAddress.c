/*
 * This solution uses an explicit free list and implements several find-fit 
 * policies for the free list. The free list insertion policy is LIFO. 
 * Finally, realloc has been optimised. It now checks if neighbouring blocks are free,
 * and utilises them if possible.  
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

/* Checks if pointer is allocated */
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Creates a header which includes information of the length of the block
 * and whether the block is allocated or not. */
#define PACK(length, isAllocated) (length | isAllocated)

/*Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*Given block ptr bp, compute address of next and previous blocks*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Macros for getting predecessor and successor nodes */

#define PRED_P(bp) ((char *)(bp))
#define SUCC_P(bp) ((char *)(bp) + WSIZE)

#define PRED(bp) (*(char **)(bp))
#define SUCC(bp) (*(char **)(SUCC_P(bp)))

#define PUT_P(p, val) (*(unsigned int*)(p) = (unsigned int)(val))


#define MAX(x, y) ((x) > (y)? (x) : (y))

/*The following macros are used to implement different methods to manage and represent a freelist.*/

/* Change the following line to BESTFIT/FIRSTFIT/NEXTFIT in order to change the approach of choosing 
 * free blocks when allocating. */
#define BESTFIT


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

static int mm_check(void);

static int inHeap(void *bp);

static void add_node(void *bp);

static void delete_node(void *bp);

static void printBlock(void *bp);

/* Private global variables */

static char *heap_listp = 0;

/*Used to keep track of the explicit free list */
static char *free_listp = 0; 

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
	printf("init \n\n");
#endif

#ifdef NEXTFIT
	next_fitp = 0;
#endif
	free_listp = 0;
	/*Create the heap and return -1 if an error occured. (Not enough memory available) */
	if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
		return -1;
	PUT(heap_listp,0); /* Alignment padding */
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
	PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
	/* Set heap_listp to point at prologue footer. */
	heap_listp += (2*WSIZE);
    	
	/* Extend the heap by 1024 bytes, return -1 if error occurs. */
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
	printf("malloc size: %i \n\n", size);
#endif
	if(heap_listp == 0){ 
		printf("Heap doesnt exist when malloc is called");
		mm_init();
	}	

	size_t newsize;
        size_t extendsize;
	char *bp;
	
	
	if (size == 0) {
		return NULL;
	}
	
	/* Make sure that the size given as parameter is 8 byte aligned. And add overhead.
	 * */
	
	if(size <= DSIZE){
		newsize = 2*DSIZE;
	}
	else{
		newsize = ALIGN(size) + DSIZE;
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
	printf("free ptr: %p \n\n", ptr);
#endif
	size_t size = GET_SIZE(HDRP(ptr));

	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));
	coalesce(ptr);

}

/* Used to set the nextfit pointer to the next free block. */
#ifdef NEXTFIT
void setNext(void *ptr){	
	if(ptr == next_fitp){
		void *succ = SUCC(ptr);
		if(succ){
			next_fitp = succ;
		}
		else{
			next_fitp = free_listp;
		}	
	}
}
#endif

/*
 * Realloc reallocates a previously allocated memory block. 
 */
void *mm_realloc(void *ptr, size_t newSize)
{
#ifdef CHECK
	mm_check();
	printf("realloc size: %i ptr: %p \n\n", newSize, ptr);
        printf("freelistp : %p \n", free_listp);	
#endif
	void *oldptr = ptr;
	size_t oldSize;
	
	if(oldptr == NULL){
		printf("igetcalled");
		return mm_malloc(newSize);
	}
	
	/* Check if ptr is within the heap */
	if(!inHeap(oldptr)){
		return NULL;	
	}	
	/* Check if given size is 0, in that case free the block at which
	 * the pointer given as parameter is pointing at. */
	if(newSize == 0){
		mm_free(oldptr);
		return NULL;
	}
	
	/*Size of the block the pointer given as parameter is pointing at. */
	oldSize = GET_SIZE(HDRP(oldptr)) - DSIZE;
	/*If old size is equal to the size given as parameter, then there is nothing to be
	 * done. */
	if(oldSize == ALIGN(newSize)){
		return oldptr;
	}

	/*If oldsize is less than size, a new block for the new size is allocated, and the
	 * content of the old block is copied to the new block. */
	
	if(oldSize < ALIGN(newSize)){
		/* If the previous block is free, and the previous block + the current block 
		 * are big enough for the new size, the blocks are merged and the payload of 
		 * the current block is moved to the start of the previous block. 
		 * The pointer to the previous block is returned. */
		if(!GET_ALLOC(HDRP(PREV_BLKP(oldptr)))){
			size_t adjustedSize = oldSize + (GET_SIZE(HDRP(PREV_BLKP(oldptr))));
			if(adjustedSize > ALIGN(newSize)){
				delete_node(PREV_BLKP(oldptr));
#ifdef NEXTFIT
				setNext(PREV_BLKP(oldptr));
#endif
				void *prevptr = PREV_BLKP(oldptr);	
				memcpy(prevptr, oldptr, oldSize);


				int rest = (adjustedSize + DSIZE) - (ALIGN(newSize) + DSIZE);
				if(rest < 4*WSIZE){
					PUT(HDRP(prevptr), PACK((adjustedSize + DSIZE), 1));
					PUT(FTRP(prevptr), PACK((adjustedSize + DSIZE), 1));
					return prevptr;
				}

				PUT(HDRP(prevptr), PACK((ALIGN(newSize) + DSIZE), 1));
				PUT(FTRP(prevptr), PACK((ALIGN(newSize) + DSIZE), 1));
				void *restptr = NEXT_BLKP(prevptr);

	  			PUT(HDRP(restptr), PACK((rest), 0));
				PUT(FTRP(restptr), PACK((rest), 0));
				coalesce(restptr);
				return prevptr;
			}	

		}
		
		/* If the next block is free, and the current block + the next block 
		 * are big enough for the new size, the blocks are merged and the 
		 * original pointer is returned. */
		if(!GET_ALLOC(HDRP(NEXT_BLKP(oldptr)))){
			size_t adjustedSize = oldSize + (GET_SIZE(HDRP(NEXT_BLKP(oldptr))));
			if(adjustedSize > ALIGN(newSize)){
				delete_node(NEXT_BLKP(oldptr));
#ifdef NEXTFIT
				setNext(NEXT_BLKP(oldptr));
#endif
				int rest = (adjustedSize + DSIZE) - (ALIGN(newSize) + DSIZE);
				if(rest < 4*WSIZE){
					PUT(HDRP(oldptr), PACK((adjustedSize + DSIZE), 1));
			        	PUT(FTRP(oldptr), PACK((adjustedSize + DSIZE), 1));
					return oldptr;
				}
				PUT(HDRP(oldptr), PACK((ALIGN(newSize) + DSIZE), 1));
				PUT(FTRP(oldptr), PACK((ALIGN(newSize) + DSIZE), 1));
				void *restptr = NEXT_BLKP(oldptr);

				PUT(HDRP(restptr), PACK((rest), 0));
				PUT(FTRP(restptr), PACK((rest), 0));
				coalesce(restptr);
				return oldptr;
			}
		}

		/* If the previous 2 cases did not match, check if the previous and next block are free.
		 * If both are free and the combined size of those 2 blocks and the current block is big 
		 * enough for the new size, the blocks are merged and the payload of the current block is moved to
		 * the start of the previous block. The pointer to the previous block is returned.*/
		if(!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && !GET_ALLOC(HDRP(PREV_BLKP(oldptr)))){
			size_t adjustedSize = oldSize + (GET_SIZE(HDRP(NEXT_BLKP(oldptr))))
						      + (GET_SIZE(HDRP(PREV_BLKP(oldptr))));
			if(adjustedSize > ALIGN(newSize)){
				void *nextptr = NEXT_BLKP(oldptr);
				void *prevptr = PREV_BLKP(oldptr);
				delete_node(nextptr);
				delete_node(prevptr);
#ifdef NEXTFIT
				if(prevptr == next_fitp){
					setNext(prevptr);
				}
				if(nextptr == next_fitp){
					setNext(prevptr);
				}
#endif
				memcpy(prevptr, oldptr, oldSize);
				
				int rest = (adjustedSize + DSIZE) - (ALIGN(newSize) + DSIZE);
				if(rest < 4*WSIZE){
					PUT(HDRP(prevptr), PACK((adjustedSize + DSIZE), 1));
					PUT(FTRP(nextptr), PACK((adjustedSize + DSIZE), 1));
					return prevptr;
				}
				PUT(HDRP(prevptr), PACK((ALIGN(newSize) + DSIZE), 1));
				PUT(FTRP(prevptr), PACK((ALIGN(newSize) + DSIZE), 1));
				void *restptr = NEXT_BLKP(prevptr);

				PUT(HDRP(restptr), PACK((rest), 0));
				PUT(FTRP(restptr), PACK((rest), 0));
				coalesce(restptr);

				return prevptr;
			}  
		}
		/*If none of the above 3 cases match, a new block with the new size has to be allocated
		 * and the payload has to be copied to the new block. */
 		ptr = mm_malloc(newSize);
		/* If malloc fails, return the old pointer and dont reallocate. */
		if(ptr == NULL){
			return oldptr;
		}
		memcpy(ptr,oldptr, oldSize);
		mm_free(oldptr);
		
		return ptr;
	}
	else{ //oldSize > ALIGN(newSize) 
	        /* The block to be reallocated is split into an allocated block
		 * of size "newSize" and a free block consisting of the rest. 
		 * If the rest is not big enough, nothing is done. */
		printf("igetcalled \n");	
		int rest = (oldSize + DSIZE) - (ALIGN(newSize) + DSIZE);
		if(rest < 4*WSIZE){
			PUT(HDRP(oldptr), PACK((oldSize + DSIZE), 1));
			PUT(FTRP(oldptr), PACK((oldSize + DSIZE), 1));
			return oldptr;
		}
		PUT(HDRP(oldptr), PACK((ALIGN(newSize) + DSIZE), 1));
		PUT(FTRP(oldptr), PACK((ALIGN(newSize) + DSIZE), 1));
		void *restptr = NEXT_BLKP(oldptr);

		PUT(HDRP(restptr), PACK((rest), 0));
		PUT(FTRP(restptr), PACK((rest), 0));
		add_node(restptr);

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
	PUT(HDRP(bp), PACK(size, 0));		/* Free block header */
	PUT(FTRP(bp), PACK(size, 0));		/* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));	/* New epilogue header */
	
	/* Coalesce if the previous block was free */
	return coalesce(bp);
}


/* Coalesce is responsible for merging free blocks. Since the implementation uses an 
 * explicit free list, coalesce has to update the free list when merging free blocks.
 * This is done by the helper methods "add_node" and "delete_node". */
static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));
	if (prev_alloc && next_alloc) {		/* Case 1 */
		
		add_node(bp);
	}

	else if (prev_alloc && !next_alloc) {	/* Case 2 */
		char *next = NEXT_BLKP(bp);
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		delete_node(next);
		add_node(bp);
	}
	
	else if (!prev_alloc && next_alloc) {	/* Case 3 */
		char *prev = PREV_BLKP(bp);
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		delete_node(prev);
		bp = prev;
		add_node(bp);
	}

	else { // !prev_alloc && !next_alloc	/* Case 4 */	
		char *prev = PREV_BLKP(bp);
		char *next = NEXT_BLKP(bp);
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		delete_node(prev);
		delete_node(next);
		bp = PREV_BLKP(bp);
		add_node(bp);
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

/* Find_fit is responsible for traversing the free list (explicit freelist) and finding
 * an unallocated block that meets the size requirement which is given as a parameter.
 * The method implements several different policies, which can be toggled at the start of the file.*/
static void *find_fit(size_t size){
	void *bp;
/* Traverse the heap until a free block that meets the size requirement is found. */
#ifdef FIRSTFIT
	for(bp = free_listp; bp != 0; bp = SUCC(bp)){
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
		next_fitp = free_listp;
	}
	for(bp = next_fitp; bp != 0; bp = SUCC(bp)){
		char *header = HDRP(bp);
		if((!GET_ALLOC(header)) && (size <= GET_SIZE(header))){
			return bp;
		}	
	}
	
	for(bp = free_listp; bp != next_fitp && bp != 0; bp = SUCC(bp)){
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
	for(bp = free_listp; bp != 0; bp = SUCC(bp)){
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
		delete_node(bp);
		PUT(HDRP(bp), PACK(length,1));
		PUT(FTRP(bp), PACK(length,1));

/* Next fit is set here, since place is called with a free block allocated by find_fit.
 * The next fit pointer now has to be changed to point at the next free block. */
#ifdef NEXTFIT
		setNext(bp);
#endif
	}else{
		delete_node(bp);
		PUT(HDRP(bp), PACK(size,1));
		PUT(FTRP(bp), PACK(size,1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(rest,0));
		PUT(FTRP(bp), PACK(rest,0));
#ifdef NEXTFIT
		next_fitp = bp;
#endif
		coalesce(bp);

	}
}

/* add_node adds a free block to the explicit free list. 
 * This implementation uses the address-order approach, which means that
 * every block in the free list is in address order. (from low to high)*/
static void add_node(void *bp){
	/* if the free_listp is 0, the free_listp is set to point
	 * at the new free block. */
        if(free_listp == 0){
                free_listp = bp;
                PUT_P(PRED_P(bp), 0);
                PUT_P(SUCC_P(bp), 0);
        }
	/* if the new free block has an address that is less than
	 * the first free block in the free list, it is set at the
	 * start of the free list. */
        else if(bp < free_listp){
                PUT_P(PRED_P(bp), 0);
                PUT_P(SUCC_P(bp), free_listp);
                PUT_P(PRED_P(free_listp), bp);
                free_listp = bp;
        }
        else{ // free_listp != 0 && !(bp < free_listp)
		/* The free list is traversed until the right position is found. 
		 * When the position has been found, the references of the current 
		 * and next free block are updated to insert the new free block. */	
                void *travp;
                for(travp = free_listp; travp != 0; travp = SUCC(travp)){
                        /* The position for insertion is found */
                        if(travp > bp){
                                PUT_P(SUCC_P(bp), travp);
                                PUT_P(PRED_P(bp), PRED(travp));
                                PUT_P(SUCC_P(PRED(travp)), bp);
                                PUT_P(PRED_P(travp), bp);
                                return;
                        }
                        /* The block is inserted at the end of the list. */
                        else if(!SUCC(travp)){
                                PUT_P(SUCC_P(travp), bp);
                                PUT_P(PRED_P(bp), travp);
                                PUT_P(SUCC_P(bp), 0);
                        }
                }
        }
}


/* delete_node is responsible for deleting a free block from
 * the explicit free list. This is done by updating the references
 * of the predecessor and successor.*/
static void delete_node(void *bp){
	void *pred = PRED(bp);
	void *succ = SUCC(bp);	
	/* If a predecessor and successor exist,
	 * the predecessor's successor field is set 
	 * to point at the successor and the successor's
	 * predecessor field is set to point at the predecessor.*/
	if(pred && succ){
		PUT_P(SUCC_P(pred), SUCC(bp));
		PUT_P(PRED_P(succ), PRED(bp));
	}
	/* If only the successor exists, the free_listp 
	 * is set to point at the successor.*/ 
	else if(!pred && succ){
		PUT_P(PRED_P(succ), 0);
		free_listp = succ;
	}
	/* If only the predecessor exists, the 
	 * predecessor's successor is set to 0. */
	else if( pred && !succ){
		PUT_P(SUCC_P(pred), 0);
	}
	/* If both do not exist, the free_listp is set to 0. */
	else{ // !pred && !succ
		free_listp = 0;
#ifdef NEXTFIT
		next_fitp = 0;
#endif
	}
}

/* Returns whether the pointer given as parameter is in heap or not. */
static int inHeap(void *bp){
	return (bp > mem_heap_lo() && bp < mem_heap_hi());
}

/* Prints all information associated with the block pointed at
 * by the pointer given as parameter. */
static void printBlock(void *bp){
	printf("Block address: %p \n", bp);
	printf("Header size: %i \n", GET_SIZE(HDRP(bp)));
	printf("Header alloc: %i \n", GET_ALLOC(HDRP(bp)));
	printf("Predecessor: %p \n", PRED(bp));
	printf("Footer size: %i \n", GET_SIZE(FTRP(bp)));
	printf("Footer alloc: %i \n", GET_ALLOC(FTRP(bp)));
	printf("Successor: %p \n", SUCC(bp));
	printf("----------------\n");
}

#ifdef CHECK
/* Checks if the block given as parameter is 8 byte aligned and the
 * footer and header are equal. */
static int blockCheck(void *bp){
	int error = 0;
	if(((size_t) bp % 8)){
		printf("payload not aligned \n");
		error = 1;
	}
	if(GET(HDRP(bp)) != GET(FTRP(bp))){
		printf("footer and header not equal \n");
		printf("footer: %i header: %i \n", GET(FTRP(bp)), GET(HDRP(bp)));
		error = 1;
	}

	return error;
}	

/* This method is currently not used, but was made for debugging purposes.
 * freelistCheck prints all free blocks on the free list and checks for pointers
 * that point outside of the heap. */
static int freelistCheck(void){
	int error = 0;
	void *bp;
	if(free_listp && PRED(free_listp)){
		printf("ERROR freelist \n");
		error = 1;
	}
	for(bp = free_listp; bp != 0; bp = SUCC(bp)){
		if(!inHeap(bp)){
			printf("Traversal failed \n");
			error = 1;
			break;
		}
		printBlock(bp);
		error = blockCheck(bp);
	}
	return error;
}

/* mm_check is a debugging method that can be toggled at the start of the file. */
static int mm_check(void){
	int error = 0;
	error = blockCheck(heap_listp);

	if(GET_SIZE(HDRP(heap_listp)) != DSIZE){
		printf("Broken prologue size \n");
		error = 1;
	}
	if(!(GET_ALLOC(HDRP(heap_listp)))){
		printf("broken prologue allocate \n");
		error = 1;
	}

	/* traverse the heap */
	void *bp;
	for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
		if(!inHeap(bp)){
			printf("Traversal failed \n");
			error = 1;
			break;
		}
#ifdef PRINTCHECK
		printBlock(bp);
#endif
		error = blockCheck(bp);
	}
	// remove comment if you want to check the freelist.
	//freelistCheck();
	/* Check epilogue header */
	if(!GET_ALLOC(HDRP(bp))){
		printf("Broken epilogue header \n");
		error = 1;
	}
	if((GET_SIZE(HDRP(bp))) != 0){
		printf("broken epilogue size \n");
	}
	printf("\n\n");
	if(error == 1) exit(1);
	
	return error; 
}
#endif
