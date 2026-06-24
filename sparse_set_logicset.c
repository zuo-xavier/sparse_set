#include <limits.h>
#include <stddef.h>


typedef struct {
    int* dense; 
    int* sparse;
    int sizeD; 
    int n; 
} sparse_set_t;



/*@ 
predicate dom_ran(int* a, int n ) = 
    0 <= n && 
    \valid(a + (0..n-1)) &&
    \forall integer i; 0 <= i < n ==> 0 <= a[i] < n;
*/


/*@
axiomatic to_logic_set {
    logic set<integer> to_ls{L}(sparse_set_t sparse_s, integer size)
        reads sparse_s;
    
    axiom to_ls_empty{L} : \forall sparse_set_t sparse_s, integer size; 
        to_ls{L}(sparse_s, 0) == \empty;

    axiom to_ls_add{L} : \forall sparse_set_t sparse_s, integer size; 
        size > 0 ==> to_ls{L}(sparse_s,size) == \union(to_ls{L}(sparse_s,size-1), sparse_s.dense[size-1]);
}
*/

/*@
predicate still_in{L}(sparse_set_t s) = 
\forall integer a; a \in to_ls{L}(s, s.sizeD)
 ==> a \in to_ls(s,s.sizeD);

*/


/*@
predicate inv1(sparse_set_t sparse_set) = 
    dom_ran(sparse_set.dense, sparse_set.n) && dom_ran(sparse_set.sparse, sparse_set.n);

predicate inv2(sparse_set_t sparse_set) = 
    0 <= sparse_set.sizeD <= sparse_set.n; 

predicate inv3(sparse_set_t sparse_set) = 
    \forall int i, v; 0 <= i < sparse_set.n && 0 <= v < sparse_set.n ==> 
    (sparse_set.dense[i] == v <==> sparse_set.sparse[v] == i);

predicate inv4(sparse_set_t sparse_set) = 
    \subset(to_ls(sparse_set, sparse_set.sizeD), (0..sparse_set.n -1));

predicate inv5(sparse_set_t sparse_set) = 
    \forall integer x; 0 <= x < sparse_set.n ==> 
        (x \in to_ls(sparse_set, sparse_set.sizeD) <==> sparse_set.sparse[x] < sparse_set.sizeD);

*/

/*@
predicate inv_sparse_set(sparse_set_t sparse_set) = 
    inv1(sparse_set) && 
    inv2(sparse_set) &&
    inv3(sparse_set) && 
    inv4(sparse_set) && 
    inv5(sparse_set);
*/
/*@
requires 0 <= n < INT_MAX;
requires \valid(dense + (0..n-1)) && \valid(sparse + (0..n-1));
requires \separated(dense + (0..n-1), sparse + (0..n-1));

assigns dense[0..n-1], sparse[0..n-1];

ensures inv_sparse_set(\result);

*/

sparse_set_t create_sparse_set(int* dense, int* sparse, int n){

    sparse_set_t sparse_set;
    sparse_set.dense = dense;
    sparse_set.sparse = sparse;
    sparse_set.sizeD = n; 
    sparse_set.n = n;

    /*@
    loop invariant 0 <= i <= n; 
    loop invariant \forall int j; 0 <= j < i ==> 
        (sparse_set.dense[j] == j && sparse_set.sparse[j] == j); 

    loop invariant \subset(to_ls(sparse_set,i), (0..n-1));
    loop invariant \forall integer x; 0 <= x < i ==>
        (x \in to_ls(sparse_set, i) ==> 0 <= sparse_set.sparse[x] < i);
    
    loop invariant \forall integer x; 0 <= x < i ==>
        (0 <= sparse_set.sparse[x] < i ==> x \in to_ls(sparse_set, i) );
        
    loop assigns sparse_set.dense[0..n-1], sparse_set.sparse[0..n-1], i;
    loop variant n-i;
    */
    for (int i = 0; i<n ; i++){
        sparse_set.dense[i] = i; 
        sparse_set.sparse[i] = i;
    }

    return sparse_set;
}

/*@
requires inv_sparse_set(sparse_set);
assigns \nothing;

ensures \result == sparse_set.sizeD;
ensures inv_sparse_set(sparse_set);
*/
int card(sparse_set_t sparse_set){
    return sparse_set.sizeD;
}


/*@
requires inv_sparse_set(sparse_set);
requires \valid_read(&sparse_set);
requires 0 <= val < INT_MAX;
assigns \nothing;

ensures inv_sparse_set(sparse_set);
behavior mem : 
    assumes val >= 0 && val < sparse_set.n;
    ensures \result == sparse_set.sparse[val] < sparse_set.sizeD;
behavior notmem: 
    assumes !(val >= 0 && val < sparse_set.n);
    ensures \result == 0 ;

complete behaviors;
disjoint behaviors;
*/
int member(sparse_set_t sparse_set, int val) {
    if (val >= 0 && val < sparse_set.n) 
        return (sparse_set.sparse[val] < sparse_set.sizeD);
    else return 0;
}


/*@
requires \valid(a) && \valid(b);
assigns *a, *b;

ensures \old(*a) == *b && \old(*b) == *a;
*/

void swap(int *a, int* b){
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

/*@
requires \forall integer k; 0 <= k < len ==> 0 <= a[k] < len;
requires 0 <= len < INT_MAX;
requires 0 <= i < len;
requires 0 <= j < len;
requires \valid(a + (0..len-1));
assigns a[0..len-1];

ensures \old(a[i]) == a[j] && \old(a[j]) == a[i];
ensures \forall integer k; (0 <= k < len && k != i && k != j) ==> \old(a[k]) == a[k]; 
*/

void swap_array(int* a, int i, int j, int len){
    int tmp = a[i];
    a[i] = a[j];
    a[j] = tmp;
}



/*@
requires inv_sparse_set(*sparse_set);
requires \valid(sparse_set);
requires 0 <= elem < sparse_set->n;
requires sparse_set->sizeD < sparse_set->n < INT_MAX;
requires \separated(sparse_set->dense + (0..sparse_set->n-1),sparse_set->sparse + (0..sparse_set->n-1), &sparse_set->sizeD, &sparse_set->n);
assigns sparse_set->dense[0..sparse_set->n-1], sparse_set->sparse[0..sparse_set->n-1], sparse_set->sizeD;

behavior notadd : 
    assumes !(0 <= elem <sparse_set->n && !(sparse_set->sparse[elem] < sparse_set->sizeD));
    ensures to_ls{Pre}(\old(*sparse_set),\old(sparse_set->n)) == to_ls(*sparse_set, sparse_set->n);
    ensures inv_sparse_set(*sparse_set);

behavior add : 
    assumes (0 <= elem < sparse_set->n) && !(sparse_set->sparse[elem] < sparse_set->sizeD);
    ensures sparse_set->sizeD == \old(sparse_set->sizeD) +1;

    ensures to_ls(*sparse_set,sparse_set->sizeD) == \union(elem, to_ls{Pre}(*sparse_set, sparse_set->sizeD));
    ensures inv1(*sparse_set);
    ensures inv2(*sparse_set);
    ensures inv3(*sparse_set);
    ensures inv4(*sparse_set);
    ensures inv5(*sparse_set);

complete behaviors;
disjoint behaviors;

*/
void add(sparse_set_t* sparse_set, int elem){

    if (elem >= 0 && elem <sparse_set->n && !(sparse_set->sparse[elem] < sparse_set->sizeD)) {

        int elem_position = sparse_set->sparse[elem];
        int border_elem = sparse_set->dense[sparse_set->sizeD];

        
        //@assert \forall integer i; 0 <= i < sparse_set->n ==> 0 <= sparse_set->sparse[i] < sparse_set->n;

        //swap(sparse_set->sparse + elem, sparse_set->sparse + border_elem);
        swap_array(sparse_set->sparse, elem, border_elem, sparse_set->n);
        L: ;
        //@assert sparse_set->sparse[elem] == sparse_set->sizeD;
        //@assert sparse_set->sparse[border_elem] == elem_position;

        
        //@assert \forall integer k; 0 <= k < sparse_set->n ==> sparse_set->dense[k] == \at(sparse_set->dense[k], Pre);        
        //@assert sparse_set->n == \at(sparse_set->n, Pre);
        
        //swap(sparse_set->dense + elem_position, sparse_set->dense + sparse_set->sizeD);
        swap_array(sparse_set->dense, elem_position, sparse_set->sizeD, sparse_set->n);
        //@assert sparse_set->dense[elem_position] == border_elem;
        //@assert sparse_set->dense[sparse_set->sizeD] == elem; 


        //@assert \forall integer k; 0 <= k < sparse_set->n ==> sparse_set->sparse[k] == \at(sparse_set->sparse[k], L);

        //@assert sparse_set->sparse[elem] == sparse_set->sizeD;
        sparse_set->sizeD++;
        //@assert sparse_set->sparse[elem] < sparse_set->sizeD;

        //@assert elem \in to_ls(*sparse_set, sparse_set->sizeD);
        //@assert still_in{Pre}(*sparse_set);

        //@assert sparse_set->n == \at(sparse_set->n, Pre);
        //@assert  0 <= sparse_set->n; 
        //@assert \valid(sparse_set->sparse + (0..sparse_set->n-1)) ;
        //@assert \forall integer i; 0 <= i < sparse_set->n ==> 0 <= sparse_set->sparse[i] < sparse_set->n;
    

    }
}


/*@
requires \valid(sparse_set);
requires inv_sparse_set(*sparse_set);
requires \separated(sparse_set->dense + (0..sparse_set->n-1),sparse_set->sparse + (0..sparse_set->n-1), &sparse_set->sizeD, &sparse_set->n);
assigns sparse_set->sizeD;

behavior incr : 
    assumes sparse_set->sizeD < sparse_set->n; 
    ensures \old(sparse_set->sizeD) + 1 == sparse_set->sizeD;
    ensures  inv1(*sparse_set);
    ensures  inv2(*sparse_set);
    ensures  inv3(*sparse_set);
    ensures  inv4(*sparse_set);
    ensures  inv5(*sparse_set);
*/
void expand_sparse_set(sparse_set_t *sparse_set){
    if(sparse_set->sizeD < sparse_set->n){

        //@assert inv5(*sparse_set);
        sparse_set->sizeD++;

        //@assert \forall integer x; 0 <= x < sparse_set->n ==> (x \in to_ls(*sparse_set, sparse_set->sizeD) ==> sparse_set->sparse[x] < sparse_set->sizeD);

        //@assert \forall integer x; 0 <= x < sparse_set->n ==> ( sparse_set->sparse[x] < sparse_set->sizeD ==> x \in to_ls(*sparse_set, sparse_set->sizeD));

        //@assert inv5(*sparse_set);


        //@assert \subset(to_ls(*sparse_set, sparse_set->n), (0..sparse_set->n -1));

        //@assert \forall integer i; 0 <= i < sparse_set->n ==> sparse_set->sparse[i] == \at(sparse_set->sparse[i], Pre);
        //@assert \forall integer i; 0 <= i < sparse_set->n ==> sparse_set->dense[i] == \at(sparse_set->dense[i], Pre);

        //@assert dom_ran(sparse_set->sparse,sparse_set->n);
        //@assert dom_ran(sparse_set->dense,sparse_set->n);
        //@assert sparse_set->sizeD == \at(sparse_set->sizeD,Pre) +1;
    }
}

/*@
lemma oui: 
    \forall sparse_set_t s; inv1(s) ==> \subset(to_ls(s,s.n), (0..s.n-1));

lemma oui2: 
    \forall sparse_set_t s; \subset(to_ls(s,s.n), (0..s.n-1)) ==> \subset(to_ls(s,s.sizeD), (0..s.n-1));
*/
