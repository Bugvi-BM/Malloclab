We started out by implementing an implicit free list. For the implicit list implementation 
we implemented 3 different find-fit policies and removed the footer in allocated blocks. 
This solution can be found in "mmImplicit.c"

Then we implemented an explicit free list with LIFO insertion policy. We also implemented
3 different find-fit policies for this solution.
This solution can be found in "mmExplicitLIFO.c"  

Next, we changed the LIFO insertion policy on the explicit list to address-based. 
This solution can be found in "mmExplicitAddress.c"

Then we implemented a segregated free list with LIFO insertion policy. 
This solution can be found in "mm.c"

Finally, we tried to maximize utilisation for the realloc traces by changing 
the "place" method. We think that this change only makes sense for the very specific problem domain
of this assignment.
This solution can be found in "mmSegregatedHacky.c"

Interesting findings:

We observed that an implicit free list that uses the next fit policy,
is almost as fast as an explicit free list using best fit. 

The difference between the address and lifo implementation for the explicit free list was not noticeable. 
Both in terms of throughput and utilisation.

We observed a significant increase in throughput when we implemented the segregated free list. The score however, did 
not change since the explicit free list implementation already had full throughput points. 
