
/*
 * This solution is similar to the mmSegregated.c file, but tries to 
 * improve the utilisation for the realloc traces. This improvement however,
 * is only relevant for the specific traces. We think that it would not be a 
 * good idea to include these changes in a general-purpose dynamic memory allocator.  
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

#define LISTLIMIT 20

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

/* Used to enable/disable the heap checker. */
//#define CHECK

/* Only works when "CHECK" is defined. Prints out each block in the heap for every time
 * malloc, realloc, free and init is called. */
//#define PRINTCHECK


/* Forward declaration */
static void *extend_heap(size_t words);

static void *coalesce(void *bp);

static void *find_fit(size_t newsize);

static void *place(void *bp, size_t newsize);

static int mm_check(void);

static int inHeap(void *bp);

static void add_node(void *bp);

static void delete_node(void *bp);

static void printBlock(void *bp);

static int freelistCheck(void);

/* Private global variables */

static char *heap_listp = 0;

/*Used to keep track of the explicit free list */
static char *segregated_freelists[LISTLIMIT]; 

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
#ifdef PRINTCHECK
	printf("init \n\n");
#endif

	/* Initialise the segregated free list */
	for(int i = 0; i < LISTLIMIT; i++){
		segregated_freelists[i] = NULL;
	}

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
#endif
#ifdef PRINTCHECK
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
		return place(bp, newsize);
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
	return place(bp, newsize);
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
#endif
#ifdef PRINTCHECK
	printf("free ptr: %p \n\n", ptr);
#endif
	size_t size = GET_SIZE(HDRP(ptr));

	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));
	coalesce(ptr);

}

/*
 * Realloc reallocates a previously allocated memory block. 
 */
void *mm_realloc(void *ptr, size_t newSize)
{
#ifdef CHECK
	mm_check();
#endif
#ifdef PRINTCHECK
	printf("realloc size: %i ptr: %p \n\n", newSize, ptr);	
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
				void *prevptr = PREV_BLKP(oldptr);	
				memcpy(prevptr, oldptr, oldSize);


				int rest = (adjustedSize + DSIZE) - (ALIGN(newSize) + DSIZE);
				if(rest < 4*WSIZE){
					PUT(HDRP(prevptr), PACK((adjustedSize + DSIZE), 1));
					PUT(FTRP(prevptr), PACK((adjustedSize + DSIZE), 1));
					return prevptr;
				}

				PUT(HDRP(prevptr), PACK((adjustedSize + DSIZE), 1));
				PUT(FTRP(prevptr), PACK((adjustedSize + DSIZE), 1));
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
				int rest = (adjustedSize + DSIZE) - (ALIGN(newSize) + DSIZE);
				if(rest < 4*WSIZE){
					PUT(HDRP(oldptr), PACK((adjustedSize + DSIZE), 1));
			        	PUT(FTRP(oldptr), PACK((adjustedSize + DSIZE), 1));
					return oldptr;
				}
				PUT(HDRP(oldptr), PACK((adjustedSize + DSIZE), 1));
				PUT(FTRP(oldptr), PACK((adjustedSize + DSIZE), 1));
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
				memcpy(prevptr, oldptr, oldSize);
				
				int rest = (adjustedSize + DSIZE) - (ALIGN(newSize) + DSIZE);
				if(rest < 4*WSIZE){
					PUT(HDRP(prevptr), PACK((adjustedSize + DSIZE), 1));
					PUT(FTRP(nextptr), PACK((adjustedSize + DSIZE), 1));
					return prevptr;
				}
				PUT(HDRP(prevptr), PACK((adjustedSize + DSIZE), 1));
				PUT(FTRP(prevptr), PACK((adjustedSize + DSIZE), 1));

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
		delete_node(next);
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		add_node(bp);
	}
	
	else if (!prev_alloc && next_alloc) {	/* Case 3 */
		char *prev = PREV_BLKP(bp);
		delete_node(prev);
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = prev;
		add_node(bp);
	}

	else { // !prev_alloc && !next_alloc	/* Case 4 */	
		
		char *prev = PREV_BLKP(bp);
		char *next = NEXT_BLKP(bp);
		
		delete_node(prev);
		delete_node(next);
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		add_node(bp);
	}

	return bp;
}

/* Find_fit is responsible for traversing the free list (segregated freelist) and finding
 * an unallocated block that meets the size requirement which is given as a parameter.
 * The method implements several different policies, which can be toggled at the start of the file.*/
static void *find_fit(size_t size){
	int listcount;
	void *bp = NULL;
	size_t bitshift = size;
	for(listcount = 0; listcount < LISTLIMIT; listcount++){
		if((listcount == LISTLIMIT - 1) || ((bitshift <= 1) && (segregated_freelists[listcount] != NULL))){
			bp = segregated_freelists[listcount];
			
			while((bp != NULL) && ((size > GET_SIZE(HDRP(bp))))){
				bp = SUCC(bp);		
			}
			if(bp != NULL){
				break;
			}
		}
		bitshift = bitshift >> 1;
	}
	return bp;
}

/* Place is responsible for splitting a free block into an allocated block
 * consisting of the size given as parameter and a free block consisting of the rest
 * of the original free block. If the rest is not big enough, the whole free block is allocated.*/
static void *place(void *bp, size_t size){

	size_t length = GET_SIZE(HDRP(bp));
	size_t rest = length - size;
	delete_node(bp);
	if((rest) < (4*WSIZE)){
		PUT(HDRP(bp), PACK(length,1));
		PUT(FTRP(bp), PACK(length,1));
	}else if(size >= 200){
		PUT(HDRP(bp), PACK(rest,0));
		PUT(FTRP(bp), PACK(rest,0));
		add_node(bp);
		
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(size,1));
		PUT(FTRP(bp), PACK(size,1));
	}else{
		PUT(HDRP(bp), PACK(size,1));
		PUT(FTRP(bp), PACK(size,1));
		bp = NEXT_BLKP(bp);	
		PUT(HDRP(bp), PACK(rest,0));
		PUT(FTRP(bp), PACK(rest,0));
		add_node(bp);
		bp = PREV_BLKP(bp);
		

	}
	return bp;
}

/* add_node adds a free block to the explicit free list. 
 * This implementation uses the LIFO approach, which means that
 * the node is added at the start of the free list and set to point
 * at the previous first node. */
static void add_node(void *bp){
	
	int listcount = 0;
	void *freelistp;
	size_t size = GET_SIZE(HDRP(bp));
	while((size > 1) && listcount < (LISTLIMIT - 1)){
		size = size >> 1;
		listcount++;
	}

	freelistp = segregated_freelists[listcount];

	if(freelistp == 0){
		PUT_P(PRED_P(bp), 0);
		PUT_P(SUCC_P(bp), 0);
		segregated_freelists[listcount] = bp;
	}
	else{
		PUT_P(PRED_P(bp), 0);
		PUT_P(SUCC_P(bp), freelistp);
		PUT_P(PRED_P(freelistp), bp);
		segregated_freelists[listcount] = bp;
	}
}

/* delete_node is responsible for deleting a free block from
 * the explicit free list. This is done by updating the references
 * of the predecessor and successor.*/
static void delete_node(void *bp){
	int listcount = 0;
	size_t size = GET_SIZE(HDRP(bp));
	while((size > 1) && listcount < (LISTLIMIT - 1)){
		size = size >> 1;
		listcount++; 
	}
	
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
		segregated_freelists[listcount] = succ;
	}
	/* If only the predecessor exists, the 
	 * predecessor's successor is set to 0. */
	else if( pred && !succ){
		PUT_P(SUCC_P(pred), 0);
	}
	/* If both do not exist, the free_listp is set to 0. */
	else{ // !pred && !succ
		segregated_freelists[listcount] = 0;
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

/* FreelistCheck prints all free blocks on the free list and applies various checks for consistency. */
static int freelistCheck(void){
        int error = 0;
#ifdef PRINTCHECK
        printf("segregated freelist: \n");
#endif
        for(int i = 0; i < LISTLIMIT; i++){
#ifdef PRINTCHECK
                printf("list %i -> %p", i, segregated_freelists[i]);
#endif
                void *bp = segregated_freelists[i];

                if (bp != NULL){
                        while(SUCC(bp) != NULL){
                                if(!inHeap(bp)){
                                        printf("Freelist error: Not in heap! \n");
                                        error = 1;
                                }
                                if(GET_ALLOC(HDRP(bp)) || GET_ALLOC(FTRP(bp))){
                                        printf("Freelist error: block on free list is allocated! \n");
                                        error = 1;
                                }
                                bp = SUCC(bp);
#ifdef PRINTCHECK
                                printf(" -> %p", bp);
#endif
                        }
                }
#ifdef PRINTCHECK
                printf("\n");
#endif
        }
        return error;
}


#ifdef CHECK
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
        freelistCheck();
#ifdef PRINTCHECK
        printBlock(bp);
#endif
        /* Check epilogue header */
        if(!GET_ALLOC(HDRP(bp))){
                printf("Broken epilogue header \n");
                error = 1;
        }
        if((GET_SIZE(HDRP(bp))) != 0){
                printf("broken epilogue size \n");
        }
#ifdef PRINTCHECK
        printf("\n\n");
#endif
        if(error == 1) exit(1);

        return error;
}
#endif

