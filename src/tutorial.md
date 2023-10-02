---
title: 'Getting Started with Anchor'
author: Cormac Flanagan and Stephen Freund
---

\define{mover}{<span class="mover font-weight-bold">#1</span>}
\define{kword}{<span class="keyword">#1</span>}
\define{const}{<span class="const">#1</span>}
\define{anchor}{<span class="smallcaps">Anchor</span>}
\define{tool}{\anchor}
\define{inline}{`#1`{.anchor}}

\define{MR}{\mover{R}}
\define{ML}{\mover{L}}
\define{MB}{\mover{B}}
\define{MN}{\mover{N}}
\define{ME}{\mover{E}}
\define{MI}{\mover{<span class="invisible">E</span>}}

\define{B}{<span class="btn btn-success btn-small btn-mover rounded-circle ff">#1</span>}
\define{BR}{<span class="btn btn-success btn-small btn-mover rounded-circle ff u-step invisible">#1</span>}
\define{BY}{<span class="btn btn-primary btn-small ff btn-mover">Y</span>}
\define{BS}{<span class="btn btn-small ff btn-light btn-fold"><i class="fas fa-ellipsis-h"></i></span>}
\define{BH}{<span class="btn btn-warning btn-small btn-heap ff"><i class="fas fa-sitemap"></i></span>}

\define{BMR}{\B{R}}
\define{BML}{\B{L}}
\define{BMB}{\B{B}}
\define{BMN}{\B{N}}
\define{BME}{\B{E}}

\define{redpat}{\MR\*;\MN?;\ML\*}

\define{question}{
  **Exercise.** #1
}

\define{t}{`#1`}

\define{code}{
```anchor#1
```
}

\define{code2}{
```anchor#1
/*****/#2
```
}


\define{codeSnip}{
```anchor#1
/*****/
class Example {#1}
```
}

\define{verify}{
```anchor#1
/*****/
/*****/
VERIFY
```
}

\define{verify2}{
```anchor#1
/*****/#2
/*****/
VERIFY
```
}

\define{verifySnip}{
```anchor#1
/*****/
class Example {#1}
/*****/
VERIFY
```
}


\define{buggy}{
```anchor#1
/*****/
/*****/
VERIFY_BUGGY
```
}

\define{buggy2}{
```anchor#1
/*****/#2
/*****/
VERIFY_BUGGY
```
}

\define{buggySnip}{
```anchor#1
/*****/
class Example {#1}
/*****/
VERIFY_BUGGY
```
}



## Welcome!

Writing correct concurrent code can be a daunting task for even the most expert programmer.
\tool is designed to make that task easier by verifying that code is free of concurrency errors and also behaves as the programmer intended.
To use \tool, a programmer adds annotations to code written in a subset of Java that enable \tool to verify key correctness properties.  You can get a sneak peak of thsese annotations by copying the following code snippet to the editor by clicking <i class="far fa-copy"></i>.  (And you can copy and then verify the snippet by clicking <i class="fas fa-anchor"></i>).  

\verify2{
class Stack { 
  ...
}
}{
class Node {
  int item  moves_as isLocal(this) ? B : (isRead() ? B : E);
  Node next moves_as isLocal(this) ? B : (isRead() ? B : E);

  Node(int item, Node next) {
    this.item = item;
    this.next = next;
  }
}

class Stack {

  Node head moves_as holds(this) ? B : E;

  modifies this;
  ensures this.head.next == old(this.head);
  ensures this.head.item == item;
  public void push(int item) {
    acquire(this);
    Node node = new Node(item, this.head);
    this.head = node; 
    release(this);
  }

  modifies this;
  ensures old(this.head) != null;
  ensures $result == old(this.head.item); 
  ensures this.head == old(this.head.next);
  public int pop() {
    acquire(this);
    while (this.head == null) 
      invariant holds(this);
    {
      release(this);
      yield;
      acquire(this);
    }
    int value = this.head.item;
    this.head = this.head.next;
    release(this);
    return value;
  }
}
}


This example is a thread-safe `Stack` that represents the stack as a linked list of `Node` objects and protects accesses to its `head` field with the enclosing `Stack` object's lock.  \tool verifies five properties for `Stack`:

1. The code satisfies the [synchronization specifications](#synchronization-specifications) on memory locations that describe the conditions under which accesses are allowed and how those accesses *commute* with steps of other threads.
2. The code is free of [data race conditions](#validity) (and hence exhibits sequentially-consistent behavior),
3. All methods are [P/C equivalent](#pc-equivalence), meaning that `yield` annotations document all location in the source where thread interference may occur.
4. All methods satisfy their [method specifications](#method-specifications).
5. The program does not go wrong due to [assertion failures](#assertions-and-debugging).

Some of these guarantees may be familiar, while others may need some explanation.  We illustrate all of them below, and 
while using \tool doesn't make concurrent programmer trivial, it does provide an effective means to document and check synchronization disciplines and expectated behavior.

This tutorial illustrates how to use \tool on a variety of examples.  The techniques are perhaps most accessible to those already somewhat familiar with program verification.  For those who might prefer to gain an understanding of verification of sequential code before diving into concurrency, we highly recommend checking out [Dafny](https://rise4fun.com/Dafny/tutorial).  Indeed, many aspects of our work on \tool are inspired by earlier tools like Dafny.

To understand the annotations we've added for \tool, we first take a brief tour of the theory underlying our technique...

## Lipton's Theory of Reduction

\anchor's reasoning is based on Lipton's theory of
reduction.  Specifically, \anchor reasons about how memory and synchronization operations of
a thread commute with concurrent operations of other threads:

* \MR: An operation is a right-mover if it can
  commute *to the right* of any subsequent operation by a different
  thread without changing the resulting state.  For example, a lock
  acquire by is a right-mover because any subsequent operation by another thread cannot
  modify that lock.

* \ML: An operation is a left-mover if it can commute *to the left* of a preceding 
operation by a different
  thread without changing the resulting state. 
  For example, a lock release is a left-mover because any
  preceding operation by another thread cannot
  modify that lock.

* \MB: An operation is a both-mover if it is both a
  left and a right mover.  For example, a race-free memory
  access is a both-mover because there are no concurrent,
  conflicting accesses.

* \MN: operation is a non-mover if it is 
  neither a left- nor a right-mover.  For example, an access to a 
  race-prone variable is a non-mover since there may be concurrent writes.


Consider a sequence of steps performed by a particular thread that consists of

* zero or more right-movers (\MR);
* at most one non-mover (\MN); and
* zero or more left-movers (\ML).

Such a sequence \MR\*;\MN?;\ML\* is *reducible*;
any interleaved steps of other threads can be "commuted out" to
yield an execution in which the steps run in a cooperative fashion
without interleaved steps from other threads.  For example, a lock
acquire followed by race-free memory accesses and then a lock release
is reducible.  The figure below illustrates how such a sequence of
steps interleaved with steps of other threads may be commuted within a
trace to produce a sequence with the same behavior, but without
interleaved steps.  

<div class="d-flex justify-content-center">
|  Original Trace   |  | Trace after Reduction  |
| ------------------------------ | ----| -------------------------------------------- |
| \MR     `acquire(m)`                         |  |  \MI <span style="color:darkred;">...</span> |
| \MI <span style="color:darkred;">...</span> |  |  \MI <span style="color:darkred;">...</span> |
| \MB     `tmp = this.x`                       |  |  \MR     `acquire(m)`                         |  
| \MI <span style="color:darkred;">...</span> |  |  \MB     `tmp = this.x`                       |
| \MB     `this.x = tmp + 1`                   |  |  \MB     `this.x = tmp + 1`                   |
| \MI <span style="color:darkred;">...</span> |  |  \ML     `release(m)`                         |
| \ML     `release(m)`                         |  |  \MI <span style="color:darkred;">...</span> |
</div>

\tool uses this theory to show that each method
is [P/C equivalent](#pc-equivalence) by verifying that all execution paths consist
of reducible sequences <p style="text-align:center;">\MR\*;\MN?;\ML\*</p> separated by yields. 





## Synchronization Specifications

To leverage Lipton's theory,
\tool relies on synchronization specifications that
describe both

1. when each thread is permitted to access (read or write) each shared memory location, and
2. how each permitted access *commutes* with potential concurrent accesses of other threads.

A basic synchronization specification is one of the standard mover
classifications (\MR, \ML, \MB, \MN) or the special
*error mover* \ME to indicate that an access is not
permitted.  Commutativity can also be conditioned on
a boolean expression.

As an example, consider the field `head` in our `Stack` example above. 
It protected by the lock of the
enclosing object.  If a thread accesses `head` without holding that lock, 
it is an error (denoted \ME in our specification language).
If a thread holds that lock, then an access to `head` commutes across
preceding and succeeding operations of other threads because other
threads cannot simultaneously access that lock-protected field and is thus a both mover. 

We write this specification in \tool as a \kword{moves_as} annotation:

\verify2{
class Stack {
  Node head moves_as holds(this) ? B : E;
}
}{
class Node {
  // ...
}

class Stack {
  Node head moves_as holds(this) ? B : E;
}
}

Synchronization mechanisms are often designed around a rich variety of
conditions, including which locks are held, whether an access is a
read or a write, whether the enclosing object is thread local, the
identity of the accessing thread, and the values of other variables or
other aspects of program state.  Such conditions are readily captured
by \tool's \kword{moves_as} synchronization specifications.  

For the `Node` class in our example, both fields have a specification
indicating that accesses are both-movers as long as the node is thread-local (that is, accessible only to the current thread).
If a node is not thread-local, then its fields are readonly, meaning they have both-mover read permissions but error write permissions:

\verify2{
class Node {
  int item  moves_as isLocal(this) ? B : (isRead() ? B : E);
  Node next moves_as isLocal(this) ? B : (isRead() ? B : E);
}
}{
class Node {
  int item  moves_as isLocal(this) ? B : (isRead() ? B : E);
  Node next moves_as isLocal(this) ? B : (isRead() ? B : E);
}

class Stack {
  Node head moves_as holds(this) ? B : E;
}
}

<!-- Here's one last example in which the specification refers to the
value of a field to determine the communitivity of an access:

\verify2{
volatile int value 
    moves_as this.value != -1 ? N : (isRead() ? R : E);
}{
class Example
  // reads/writes are non-movers, until item4 becomes -1.
  // Then writes are prohibited, and reads are right-movers.
  volatile int value
      moves_as this.value != -1 ? N : (isRead() ? R : E);
}
}
 -->

The boolean expressions in \kword{moves_as} annotations can be any valid
boolean expressions and can also include the following special variables 
and predicates:

|      |        |
| ----:| ------------------------------------------------------------------------- |
| \kword{tid}           | the thread identifier of the accessing thread.     |
| \kword{isRead}`()`      | whether the access is a read.                      |          
| \kword{newValue}      | the value being written, if the access is a write.       |       
| \kword{holds}`(o)`  | whether the lock for the object denoted by the expression `o` is held. |
| \kword{isLocal}`(o)`  | whether  `o` is accessible by only the current thread. |


Array types also include \kword{moves_as} annotations capturing the permission for
accessing each array element.  Since array types can get pretty large pretty quickly, 
and are often repeated in the code, we use \kword{array} declarations to provide short
names for array types.

Here are two quick examples.  This first is a field
whose type is an array in which elements are all protected by the enclosing objects lock.  Further, the
field itself is protected by the same lock.

\verify2{
class ArrayExample {

  array UsesLock = int[moves_as holds(this) ? B : E]; 
  
  [UsesLock] elems moves_as isLocal(this) 
                            ? B 
                            : holds(this) ? B : E;

  // ...
}
}{
class ArrayExample {

  array UsesLock = int[moves_as holds(this) ? B : E];
  
  [UsesLock] elems moves_as isLocal(this) ? B : holds(this) ? B : E;

  public ArrayExample() {
    this.elems = new [UsesLock](10);
  }

  requires 0 <= i < 10;
  public void access(int i) {
    synchronized(this) {   // acquire/release around enclosed block.
      this.elems[i] == 0;
    }
  }
}
}

The second is an array in which a thread may only access the element at the 
index corresponding to its \kword{tid}.

\verify2{
array ThreadLocal = int[moves_as index == tid ? B : E];
}{
class ArrayExample {

  array ThreadLocal = int[moves_as index == tid ? B : E];

  [ThreadLocal] elems moves_as (isLocal(this) || isRead()) ? B : E;

  public ArrayExample() {
    this.elems = new [ThreadLocal](10);
  }

  requires 0 <= tid < 10;
  public void access() {
    this.elems[tid] == 0;
  }
}
}


\tool checks synchronization specifications for the following two properties: *validity* and *stability*.
These are covered next.

(One small detail to keep in mind: any field that may be given \ML, \MR, or \MN 
 commuting behavior may be prone to data races (unordered conflicting accesses).
We require those fields to be declared \kword{volatile} to ensure sequential
  consistency, which provides a strong guarantee to the
  programmer even on platforms with relaxed memory models.)


#### Validity

Synchronization specifications must exclude commuting actions that might change program state.
For example, in any context where the specification indicates that a reading a field is a right-mover,
all writes to that field must be forbidden.  Otherwise, the read could commute to the right past a write
that changes the value stored in the field.

The following specification is not valid, because it permits such reads to commute across writes.  
(Whenever we show you buggy code, we change our verify button from 
<i class="fas fa-anchor"></i> to <i class="fas fa-bug"></i>.)

\buggySnip{
  volatile int value moves_as B;
}

Attempting to verify this snippet produces a pair of operations by different threads that violate
the validity requirement.

Here is a declaration with a more interesting validity violation.  The field `value` can be updated
to any value until it becomes -1.  At that point, it becomes readonly.
The specification indicates that all reads and writes are initially non-movers until `value` does
become -1.  At that point, only reads are allowed and are both-movers.

\buggySnip{
volatile int value 
  moves_as this.value != -1 ? N : (isRead() ? B : E);
}

Verifying this code identifies a validity problem, and \tool shows a pair of steps by different threads
that commute according to the specification but that change program behavior when they do.
In particular, a read of -1 can left-commute 
past a write to the field.  However, this is problematic since the field's value might not be -1 before the write occurs, meaning the read 
will then see a different value.
We can rule out the problematic case by permitting reads of -1 to right-commute but not left-commute:

\verifySnip{
volatile int value 
  moves_as this.value != -1 ? N : (isRead() ? R : E);
}



#### Stability

The second correctness requirement for synchronization specifications is *stability*.
A synchroniation specification is stable if the permission to read or write
a field is either invariant over interleaved writes, or at least changed only in ways 
that do not invalidate \tool's reduction-based reasoning.  This is a more subtle
property that validity, but also one that doesn't come up often.  We'll talk about
it more in the [Errors](errors.html){target="_blank"} document.


## P/C Equivalence

Now that we've explored \tool's synchronization specifications, let's see what it guarantees about methods.

\tool programs include \kword{yield} annotations documenting where thread interference is observable. \tool uses the synchronization specifications to verify that these annotations are placed correctly.
As such,
\tool ensures that all \kword{public} methods exhibit the same behavior
under both

* a *preemptive* scheduler that context switches at any point, and
* a *cooperative* scheduler that context switches only at \kword{yield} annotations.

We call this guarantee
**P/C equivalence**.  It enables subsequent higher-level (formal or
informal) reasoning to be based on the more intuitive cooperative
scheduler, even though the code runs on standard, preemptive
hardware. In addition, code without \kword{yield}s is guaranteed to be
atomic.


#### Stack.push()

We'll now add a \t{push} method to \t{Stack} that creates and
inserts a new \t{Node} at \t{head}.



\verify2{
public void push(int item) {
  acquire(this);
  Node node = new Node(item, this.head);
  this.head = node; 
  release(this);
}
}{
class Node {
  int item  moves_as isLocal(this) ? B : (isRead() ? B : E);
  Node next moves_as isLocal(this) ? B : (isRead() ? B : E);

  Node(int item, Node next) {
    this.item = item;
    this.next = next;
  }
}

class Stack {
  Node head moves_as holds(this) ? B : E;

  public void push(int item) {
    acquire(this);
    Node node = new Node(item, this.head);
    this.head = node; 
    release(this);
  }
}
}


To respect the synchronization discipline, the `push` method acquires the lock on
the stack object prior to accessing \t{head}.  The \t{push()} method
is atomic (reducible) since it consists of a lock acquire (\MR), a
lock-protected read of \t{head} (\MB), initialization of a
thread-local node (\MB), a lock-protected write to \t{head} (\MB),
and a lock release (\ML), thus matching the pattern
\MR\*;\MN?;\ML\*.  

For field accesses, the synchronization
discipline is evaluated at the current program point to determine its
commutativity.  For example, the write to \t{this.head} occurs when
the lock for \t{this} is held, and evaluating the synchronization
specification for \t{head} in this context yields \MB. 

We can compare this to a broken version that fails to 
acquire the lock.  If we try to verify this code, we get a reduction
error, because the read of \t{this.head} occurs without
the lock for \t{this} held, and the specification for \t{head} 
in this context yields \ME.  (If you click on the \MB{E} icon in the
error message, you can see how \tool used the synchronization specification
to conclude that that access is an error, namely that the current thread
with id \kword{tid} does not hold the lock for \t{this}.)

\buggy2{
public void push(int item) {
  Node node = new Node(item, this.head);
  this.head = node; 
}
}{
class Node {
  int item  moves_as isLocal(this) ? B : (isRead() ? B : E);
  Node next moves_as isLocal(this) ? B : (isRead() ? B : E);

  Node(int item, Node next) {
    this.item = item;
    this.next = next;
  }
}

class Stack {
  Node head moves_as holds(this) ? B : E;

  public void push(int item) {
    Node node = new Node(item, this.head);
    this.head = node; 
  }
}
}


#### Stack.pop()


Now we'll add a pop method.
The \t{pop()} method
similarly acquires the stack's lock, but then busy waits until the
stack has at least one element in it. While waiting, it releases and
re-acquires the lock.  Here's a first attempt at writing the code,
but \tool won't be able to verify it quite yet.

\buggy2{
public int pop() {
  acquire(this);
  while (this.head == null) {
    release(this);
    acquire(this);
  }
  int value = this.head.item;
  this.head = this.head.next;
  release(this);
  return value;
}
}{
class Node {
  int item  moves_as isLocal(this) ? B : (isRead() ? B : E);
  Node next moves_as isLocal(this) ? B : (isRead() ? B : E);

  Node(int item, Node next) {
    this.item = item;
    this.next = next;
  }
}

class Stack {
  Node head moves_as holds(this) ? B : E;

  public int pop() {
    acquire(this);
    while (this.head == null) {
      release(this);
      acquire(this);
    }
    int value = this.head.item;
    this.head = this.head.next;
    release(this);
    return value;
  }
}
}

If we inspect the error message \tool reports for the code, it
tells us that \tool cannot determine that the lock for \t{this} is held at the loop head.  While
it may be clear to us that it is, we need to provide \tool 
with a loop invariant indicating that this is the case:

\buggy2{
public int pop() {
  ...
  while (this.head == null) 
    invariant holds(this);
  {
    release(this);
    acquire(this);
  }
  ...
}
}{
class Node {
  int item  moves_as isLocal(this) ? B : (isRead() ? B : E);
  Node next moves_as isLocal(this) ? B : (isRead() ? B : E);

  Node(int item, Node next) {
    this.item = item;
    this.next = next;
  }
}

class Stack {
  Node head moves_as holds(this) ? B : E;

  public int pop() {
    acquire(this);
    while (this.head == null)   
      invariant holds(this);
    {
      release(this);
      acquire(this);
    }
    int value = this.head.item;
    this.head = this.head.next;
    release(this);
    return value;
  }
}
}

For this version, \tool verifies that that loop invariant holds whenever we reach 
the top of the loop and is thus able to conclude that the access to
\kword{this}`.head` in the loop test is a both-mover.  

However,
we still get an error, this time
because the steps
taken by \t{pop} don't match our reducible pattern.  In particular,
we have a left-mover `release` followed by a right-mover `acquire`.
This indicates that other threads may change \t{head} between
the release and acquire.  Thus, we include a \kword{yield} at that
point.

\verify2{
public int pop() {
  ...
  while (this.head == null) 
    invariant holds(this);
  {
    release(this);
    yield;
    acquire(this);
  }
  ...
}
}{
class Node {
  int item  moves_as isLocal(this) ? B : (isRead() ? B : E);
  Node next moves_as isLocal(this) ? B : (isRead() ? B : E);

  Node(int item, Node next) {
    this.item = item;
    this.next = next;
  }
}

class Stack {
  Node head moves_as holds(this) ? B : E;

  public int pop() {
    acquire(this);
    while (this.head == null)   
      invariant holds(this);
    {
      release(this);
      yield;
      acquire(this);
    }
    int value = this.head.item;
    this.head = this.head.next;
    release(this);
    return value;
  }
}
}

Since \kword{yield} annotations are part of a program's
specification, they do not affect the run-time behavior of
the code.  Any call to \t{pop} performs heap operations with
the following commutivities:

<div style="text-align: center;">
\MR; [ \MB; \ML; \kword{yield}; \MR; ]* \MB; \MB; \ML;
</div>

This sequence consists of reducible subsequences \redpat separated by \kword{yield}s
and is thus P/C equivalent.  

## Assertions and Debugging

Let's now add a method to our `Stack` that uses an \kword{assert} statement.  \tool will verify
that these assertions will never fail at run time.  Unfortunately, that's not the case for
us here.  

\buggy2{
public void buggy() {
  this.push(10);
  assert this.head.item == 10;
}
}{
class Node {
  int item  moves_as isLocal(this) ? B : (isRead() ? B : E);
  Node next moves_as isLocal(this) ? B : (isRead() ? B : E);

  Node(int item, Node next) {
    this.item = item;
    this.next = next;
  }
}

class Stack {
  Node head moves_as holds(this) ? B : E;

  public void buggy() {
    this.push(10);
    assert this.head.item == 10;
  }

  public void push(int item) {
    acquire(this);
    Node node = new Node(item, this.head);
    this.head = node; 
    release(this);
  }
}
}

The first thing that happens when we try to verify if is that we get the error commutivity for the access to `this.head` 
before the lock for the \t{this} object is not held at the \kword{assert} statement.  We can see the
reasoning leading to this commutivity by clicking on the mover button \B{E} next to the \kword{assert} statement
in the error message.
We can fix the error by acquiring the lock beforehand:

\buggy2{
public void buggy() {
  this.push(10);
  acquire(this);
  assert this.head.item == 10;
  release(this);
}
}{
class Node {
  int item  moves_as isLocal(this) ? B : (isRead() ? B : E);
  Node next moves_as isLocal(this) ? B : (isRead() ? B : E);

  Node(int item, Node next) {
    this.item = item;
    this.next = next;
  }
}

class Stack {
  Node head moves_as holds(this) ? B : E;

  public void buggy() {
    this.push(10);
    acquire(this);
    assert this.head.item == 10;
    release(this);
  }

  public void push(int item) {
    acquire(this);
    Node node = new Node(item, this.head);
    this.head = node; 
    release(this);
  }
}
}

However, examination of the resulting error message indicates that the code is
no longer reducible because we
acquire the lock after releasing it in the nested call to `push`.  Clicking on the
button \BS next to the next call will show you the steps inside that call.

Adding a \kword{yield} at that point fixes the reduction error
 but results in a potential assertion failure.


\buggy2{
public void buggy() {
  this.push(10);
  yield;
  acquire(this);
  assert this.head.item == 10;
  release(this);
}
}{
class Node {
  int item  moves_as isLocal(this) ? B : (isRead() ? B : E);
  Node next moves_as isLocal(this) ? B : (isRead() ? B : E);

  Node(int item, Node next) {
    this.item = item;
    this.next = next;
  }
}

class Stack {
  Node head moves_as holds(this) ? B : E;

  public void buggy() {
    this.push(10);
    yield;
    acquire(this);
    assert this.head.item == 10;
    release(this);
  }

  public void push(int item) {
    acquire(this);
    Node node = new Node(item, this.head);
    this.head = node; 
    release(this);
  }
}
}

Clicking on the heap button \BH next to the assertion in the error message shows us the
counterexample provided by \tool's theorem prover, which shows why the assertion may fail.
Note that the value of `this.head.item` read from the heap is not 10.  We can see
where `this.head.item` became a different value by click on the heap button next to the
yield step.  This version shows both the pre-state and the post-state of the
yield, with any changes hilighted in red.  From this it is clear that, perhaps as expected,
another thread could modify `this.head` at that point in execution, lead to the subsequent assertion failure.


## Method Specifications

The last step of verifying our `Stack` is to add method specifications describing 
their intended behavior.  For the atomic method `push`, we can simply state that the method's `head`
after the call contains the newly-inserted value and a reference to the old `head`.
We also must include the standard \kword{modifies} annotation to specify which
memory locations might be modified by the method.

\verify2{
modifies this;
ensures this.head.item == item;
ensures this.head.next == old(this.head);
public void push(int item) { 
  ...
}
}{
class Node {
  int item  moves_as isLocal(this) ? B : (isRead() ? B : E);
  Node next moves_as isLocal(this) ? B : (isRead() ? B : E);

  Node(int item, Node next) {
    this.item = item;
    this.next = next;
  }
}

class Stack {
  Node head moves_as holds(this) ? B : E;

  modifies this;
  ensures this.head.item == item;
  ensures this.head.next == old(this.head);
  public void push(int item) {
    acquire(this);
    Node node = new Node(item, this.head);
    this.head = node; 
    release(this);
  }

  modifies this;
  ensures old(this.head) != null;
  ensures $result == old(this.head.item); 
  ensures this.head == old(this.head.next);
  public int pop() {
    acquire(this);
    while (this.head == null)   
      invariant holds(this);
    {
      release(this);
      yield;
      acquire(this);
    }
    int value = this.head.item;
    this.head = this.head.next;
    release(this);
    return value;
  }
}
}

The specification for \t{pop} is a bit more interesting because \t{pop} is not atomic.
Moreover, all of the reducible sequences are
no-ops, except for the very last one where we 
atomically remove a node from the stack.  That last atomic
step is what we summarize in the specification:

\verify2{
modifies this;
ensures old(this.head) != null;
ensures $result == old(this.head.item); 
ensures this.head == old(this.head.next);
public int pop() {
  acquire(this);
  while (this.head == null)   
    invariant holds(this);
  {
    release(this);
    yield;
    acquire(this);
  }
  int value = this.head.item;
  this.head = this.head.next;
  release(this);
  return value;
}
}{
class Node {
  int item  moves_as isLocal(this) ? B : (isRead() ? B : E);
  Node next moves_as isLocal(this) ? B : (isRead() ? B : E);

  Node(int item, Node next) {
    this.item = item;
    this.next = next;
  }
}

class Stack {
  Node head moves_as holds(this) ? B : E;

  modifies this;
  ensures this.head.item == item;
  ensures this.head.next == old(this.head);
  public void push(int item) {
    acquire(this);
    Node node = new Node(item, this.head);
    this.head = node; 
    release(this);
  }

  modifies this;
  ensures old(this.head) != null;
  ensures $result == old(this.head.item); 
  ensures this.head == old(this.head.next);
  public int pop() {
    acquire(this);
    while (this.head == null)   
      invariant holds(this);
    {
      release(this);
      yield;
      acquire(this);
    }
    int value = this.head.item;
    this.head = this.head.next;
    release(this);
    return value;
  }
}
}


Here, the special variable `$result` refers
to the method's return value, and terms of the form \t{old(e)}, such
as \t{old(this.head.item)}, refer to the value of $e$ at the beginning of
the yield-free region captured by the specification.  Note that
\t{old(this.head.item)} may have a different value than it had at the start
of the method call if interference occurs at a documented yield
point.  



## Non-blocking Concurrency

We can also write an alternative \t{LockFreeStack} 
that uses optimistic concurrency control instead of
a lock:

\verify2{
class Stack {

  volatile Node head moves_as N;

  modifies this;
  ensures this.head.next == old(this.head);
  ensures this.head.item == item;
  public void push(int item) {
    while (true) {
      Node next = this.head;
      Node nu = new Node(item, next);
      yield;
      if (cas(this, head, next, nu)) {
        break;
      }
    }
  }

  // ...
}
}{
$/examples/LockFreeStack.anchor
}

In this version, any thread can read or write the field \t{head} at any time.
All accesses to it are thus non-movers \MN because of the potential
for conflicting concurrent writes, so \tool requires \t{head} be
declared \t{volatile} to ensure sequential consistency.

The method \t{push()} reads \t{this.head} into \t{n}, allocates a new
node \t{nu}, and then tries to atomically change \t{this.head} from
\t{n} to \t{nu} with an atomic compare-and-swap (\kword{cas}) operation.  If
  the \kword{cas} operation fails, the code retries until it 
  succeeds.   The last iteration of the loop thus looks like this:

<div class="d-flex justify-content-center">
|   |
| ----| -------------------------- 
| `N`{.anchor} | ` n = this.head;`
| \MI | ` yield;`
| `B`{.anchor} | ` nu = ...;`
| `N`{.anchor} | ` successful-cas;`
</div> 

where succeeding \kword{cas} operation is a non-mover (\MN)
since it writes to head.  All earlier loop iterations look like this:

<div class="d-flex justify-content-center">
|   |
| ----| -------------------------- 
| `N`{.anchor} | ` n = this.head;`
| \MI | ` yield;`
| `B`{.anchor} | ` nu = ...;`
| `B`{.anchor} | ` failed-cas;`
</div> 

Our analysis permits \kword{cas} to fail
non-deterministically so we treat failing \kword{cas}
operations as both-movers (\MB). The \MB/\MN annotation in the figure
captures the \kword{cas} operation's failing/succeeding
commutativities. 

The sequence 

<div style="text-align: center;">
[ \MN; \t{yield}; \MB; \MB ]*; \MN; \t{yield}; \MB; \MN 
</div>

consists of reducible sequences separated by yields and is thus
P/C equivalent.  As in the previous example, the reducible
sequences are all no-ops, except for the last, which has the heap
effect of atomically adding the new node to the stack, as required by
\t{push()}'s specification.  The \t{pop()} method is similar.

\t{LockFreeStack}'s methods satisfy the *exact same*
specifications as \t{Sack}'s, despite using optimistic
concurrency control instead of locks!

\question{Write a non-blocking \t{pop()} method for `LockFreeStack`.}


## Ghost Fields

\tool provides basic support for data abstraction via ghost fields.
Ghost fields are present
only at verification time and not at run time,  They enable us to express
specifications using data abstraction.  For example, the following
\t{Queue} class represents a fixed-size queue as a circular buffer where
values are inserted at `tail` and removed from `head`.


\verify2{
class Queue {

  // Concrete State

  array T = int[moves_as holds(this) ? B : E];

  [T] elems moves_as isLocal(this) ? B : readonly;

  volatile int tail moves_as holds(this) ? B : E;
  volatile int head moves_as holds(this) ? B : E;

  // Abstract State

  ghost Seq<int> spec;

  invariant this.spec.length 
         == (512 + this.tail - this.head) % 512;

  invariant (forall int i :: 
    (this.head <= i < this.tail) || 
    (this.head > this.tail && 
     (this.head <= i < 512 || 0 <= i < this.tail))
    ==> this.elems[i] 
        == this.spec[(512 + i - this.head)%512]);

  ...
}
}{

axiom (forall int x, int y :: 
        0 <= x && x < y ==> x % y == x);
axiom (forall int x, int y :: 
        y <= x && x < (y+y) ==> x % y == x - y);
axiom (forall int x :: 
        0 < x ==> x % x == 0);

class Queue {

  // Concrete State

  array T = int[moves_as holds(this) ? B : E];

  [T] elems moves_as isLocal(this) ? B : readonly;

  volatile int tail moves_as holds(this) ? B : E;
  volatile int head moves_as holds(this) ? B : E;

  invariant this.elems != null && this.elems.length == 512;
  invariant 0 <= this.tail < 512;
  invariant 0 <= this.head < 512;

  // Abstract State

  ghost Seq<int> spec;

  invariant this.spec.length == (512 + this.tail - this.head) % 512;

  invariant (forall int i :: 
      (this.head <= i < this.tail) || 
      (this.head > this.tail) && (this.head <= i < 512 || 0 <= i < this.tail)
      ==> this.elems[i] == this.spec[(512 + i - this.head)%512]);

  ensures this.spec == [ ];
  public Queue() {
    // spec, head, tail all zero/empty initialized
    this.elems = new [T](512);
  }

  modifies this;
  ensures this.spec == old(this.spec) ++ [x];
  public void enqueue(int x) {
    acquire(this);
    while ((this.tail + 1) % 512 == this.head) 
      invariant holds(this); {
      release(this);
      yield;
      acquire(this);
    }
    this.elems[this.tail] = x;
    this.tail = (this.tail + 1) % 512;
    this.spec = this.spec ++ [x];
    release(this);
  }

  modifies this;
  ensures old(this.spec) == [$result] ++ this.spec;
  public int dequeue() {
    acquire(this);
    while (this.tail == this.head) 
      invariant holds(this); {
      release(this);
      yield;
      acquire(this);
    }
    int result = this.elems[this.head];
    this.head = (this.head + 1) % 512;
    this.spec = this.spec[1..SeqLen(this.spec)];
    return result;
  }
}
}

The \kword{ghost} field `spec` represents the queue as a sequence with values
added at the end and removed from the first, and we provide suitable invariants 
to ensure that the `spec` sequence matches the queue encoded by the concrete
state.  Method specifications are then written in terms of only the \kword{ghost}
field.  We update \kword{ghost} fields just as normal fields, but \tool
assumes that all updates to such fields happen while executing the "commit" step of an 
atomic block.  (Internally, that means we can treat all access to \kword{ghost} fields
as both movers...)

This example also shows how to introduce new axioms.  The modular arithmetic operator `%`
is left as an uninterpreted function by default, so here we provide axioms
capturing the modular arithmetic properties necessary to verify the code:

\code{
axiom (forall int x, int y :: 
        0 <= x && x < y ==> x % y == x);
axiom (forall int x, int y :: 
        y <= x && x < (y+y) ==> x % y == x - y);
axiom (forall int x :: 
        0 < x ==> x % x == 0);
}

\tool provides three built-in value types to add in abstraction: sequences, maps, and sets.
These types can be used in specifications but not in actual code.  These
are defined directly via the Z3 solver's underlying theories.

* `Seq<T>` is an immutable sequence of \t{T} elements,
where \t{[ ]} is the empty sequence and \t{[x]} is a single-element
sequence. Sequences support concatenation (\t{s1 ++ s2}), length
(\t{s.length}), access (\t{s[i]}, and subsequence \t{s[start..end]}
operations.  There are also builtin functions for these operators and other 
operations.  In most cases, \tool will infer the appropriate type argument `T` 
For these function calls, and it can be omitted, as in `SeqEmpty()`.

  * `SeqEmpty<T>() : Seq<T>`
  * `SeqLen<T>(Seq<T>): int`
  * `SeqConcat<T>(Seq<T>, Seq<T>) : Seq<T>`
  * `SeqNth<T>(Seq<T>, int) : T`
  * `SeqUnit<T>(T) : Seq<T>`
  * `SeqSub<T>(Seq<T>, int, int) : Seq<T>`
  * `SeqEqual<T>(Seq<T>,Seq<T>): boolean`

* `Map<K,V>` is an immutable map from type \t{K} to \t{V}.  This type
supports three functions: 

  * `MapEmpty<K,V>(): Map<K,V>`
  * `MapStore<K,V>(m, k, v): Map<K,V>`
  * `MapSelect<K,V>(m, k): V`

* `Set<T>` is an immutable set from type \t{T}.  Sets support the following: 

  * `SetEmpty<T>() : Set<T>`
  * `SetSingleton<T>(T) : Set<T>`
  * `SetUnion<T>(Set<T>, Set<T>) : Set<T>`
  * `SetAdd<T>(Set<T>, T) : Set<T>`
  * `SetRemove<T>(Set<T>, T) : Set<T>`
  * `SetContains<T>(Set<T>, T) : boolean`
  * `SetIsEqual<T>(Set<T>, Set<T>) : boolean`
  * `SetIsSubset<T>(Set<T>, Set<T>) : boolean`


Here is an example using some of these operators and functions:

\verify2{
class SeqExample {
  ...
}
}{
class SeqExample {

  ghost Seq<int> seq;

  public void functions() {
      this.seq = SeqEmpty<int>();
      this.seq = SeqUnit(4);
      this.seq = SeqConcat(this.seq, this.seq);
      assert SeqNth(this.seq, 0) == 4;
      assert SeqLen(this.seq) == 2;
  }

  public void operators() {
      this.seq = [ 4 ];
      this.seq = this.seq ++ this.seq;
      assert this.seq[0] == 4;
      assert this.seq.length == 2;
  }
}
}

## Additional Details and Features

### Abbreviations

\tool supports abbreviations for common synchronization
idioms encountered in practice.  We introduce those abbreviations here
before showing one more sophisticated example.

<div class="d-flex justify-content-center">
| | | |
| ------------------------------:| ----| -------------------------------------------- |
| `thread_local`{.anchor}  | | `isLocal(this) ? B : E`{.anchor} |
| `guarded_by(l)`{.anchor} | | `holds(l) ? B : E`{.anchor} |
| `write_guarded_by(l)`{.anchor} | | `isRead()`{.anchor} |
|  | |  `? (holds(l) ? B : N)`{.anchor} |
|  | |  `: (holds(l) ? N : E)`{.anchor} |
| `readonly`{.anchor}   |  | `isRead() ? B : E`{.anchor} |
| `immutable`{.anchor}  |   | `isRead() ? R : E`{.anchor} |
</div>

For
thread-local fields, the allocating thread initially has
exclusive access (\MB).  If the object ever becomes shared between
threads, subsequent accesses are errors (\ME).

The \const{guarded_by} abbreviation captures lock-based exclusive access,
as for \t{Stack}'s \t{head} field. The
\const{write_guarded_by} abbreviation captures a more subtle discipline
where a lock must be held for writes but not necessarily for reads.
Reads while holding the lock are both-movers (\MB) since there
cannot be concurrent writes; reads without holding the lock are
non-movers (\MN) since there may be concurrent writes; and
lock-protected writes are non-movers (\MN) since there may be
concurrent reads.

The \const{readonly} abbreviation is used when a field's value is fixed
from the moment the field becomes accessible to multiple threads.
Reads of \const{readonly} fields are both-movers.

For immutable fields, writes are forbidden (\ME), but reads are okay
and are right-movers due to the absence of subsequent writes. Reads of
immutable fields are not left-movers, however, as the field
could have changed before becoming immutable.


### Which Objects are Thread Local?

\tool uses a simple strategy to identify thread-local objects. A
newly-allocated object is thread-local until a reference to it is
stored in another object, at which point it is considered
shared. Thus, shared objects never refer to thread-local data.  The
same applies to arrays.  Also, \tool assumes that the receiver and all
objects passed as parameters to \kword{public} methods are shared, and that the
receiver of a call to a \kword{public} constructor is considered local.


### Modeling Heap Changes at Yield Points

The following shows an atomic integer class `AtomicInt` .
The synchronization specification indicates that the field `this.n` can be 
read and written when holding the self lock
and that writes must always increment \t{n}, as expressed via the
condition \t{newValue == this.n + 1}.

\verify{
class AtomicInc {

  int n 
    moves_as holds(this) 
             ? isRead() ? B 
                        : (newValue == this.n + 1 ? B : E)
             : E;
  modifies this;
  ensures this.n == old(this.n) + 1;
  ensures $result == this.n;
  int inc() {
    synchronized(this) {
      this.n = this.n + 1;
      return this.n;
    }
  }
}
}

Here is a client of our class that increments the counter twice
and asserts that the value after the second increment is larger
than the value after the first.  However, this code will not 
pass the verifier.  If you try to verify the code, \tool will
be unable to ensure that `counter.n` is not decreased during
the \kword{yield}.

\buggy2{
class AtomicIntClient {
  public void incTwice(AtomicInc counter) {
    int n = counter.inc();
    yield;
    assert counter.inc() >= n;
  }
}
}{
class AtomicInc {

  int n 
    moves_as holds(this) 
             ? isRead() ? B 
                        : (newValue == this.n + 1 ? B : E)
             : E;

  modifies this;
  ensures this.n == old(this.n) + 1;
  ensures $result == this.n;
  int inc() {
    synchronized(this) {
      this.n = this.n + 1;
      return this.n;
    }
  }
}

class AtomicIntClient {
  public void incTwice(AtomicInc counter) {
    int n = counter.inc();
    yield;
    assert counter.inc() >= n;
  }
}
}

The root cause of \tool's inability to verify this code lies in
how it models state change at \kword{yield}s.  Generally speaking,
a \kword{yield} statement is modelled as zero or
more heap updates to each memory location by other threads. Those updates
are constrained by each memory location's read access permission: the
value of any memory location for which the current thread has
right-mover read access is preserved.

This rule works for the vast majority of cases, but it may admit
changes to a field like \t{counter.n} that are not actually feasible if
updates to \t{counter.n} are restricted in some particular way, as is the case
here with the restriction that all updates must increment the old value.

This motivates our introduction of optional \kword{yields_as} annotations to
better approximate heap updates.  These annotations relate
a field's post-yield value to its pre-yield value.  For our
\t{AtomicInt} class, we include a \kword{yields_as} annotation guaranteeing
the value of \t{n} may only increase at a \kword{yield}.  With that change,
the client passes the verifier.

\verify2{
int n 
  moves_as holds(this) 
            ? isRead() ? B 
                      : (newValue == this.n + 1 ? B : E)
            : E
  yields_as newValue >= this.n;
}{
class AtomicInc {

  int n 
    moves_as holds(this) 
              ? isRead() ? B 
                        : (newValue == this.n + 1 ? B : E)
              : E
    yields_as newValue >= this.n;

  modifies this;
  ensures this.n == old(this.n) + 1;
  ensures $result == this.n;
  int inc() {
    synchronized(this) {
      this.n = this.n + 1;
      return this.n;
    }
  }
}

class AtomicIntClient {
  public void incTwice(AtomicInc counter) {
    int n = counter.inc();
    yield;
    assert counter.inc() >= n;
  }
}
}

\tool verifies
that \kword{yields_as} annotations subsume all writes permissible by the
synchronization specification and that they set up possible updates permitted by them
is reflexively and transitively closed.


### ABA Freedom

Here is a second version of the \t{AtomicInt} class that uses \kword{cas} and
optimistic concurrency control.
The synchronization specification for
the now-volatile field \t{n} 
indicates that the field can be read and written at any time (\MN)
and that writes must always increment \t{n}.

\buggy{
class AtomicInc {

  volatile int n  
    moves_as isRead() ? N
                      : (newValue == this.n + 1 ? N : E)
    yields_as newValue >= this.n;

  modifies this;
  ensures this.n == old(this.n) + 1;
  public void inc() {
    while (true) {
      int x = this.n;
      if (cas(this,n,x,x+1)) {
        break;
      }
      yield;
    }
  }
}
}

We cannot verify this code, because the read of \t{this.n} and the 
subsequent read/write in the \t{cas} operation are both non-movers.  

We could eliminate this error by inserting a \kword{yield} between them, but \tool
provides a better way based on the fact that \t{this.n} is free of ABA problems.
This means that if a
thread reads a value *A* from \t{this.n}, and then later reads the same
value *A* again, then no other thread could have changed \t{this.n} from
*A* to a different value *B*, and then back to *A* again in between
those two reads. This property helps prove absence of interference
between threads.  We can declare the \t{n} field to be \kword{noABA},
and \tool verifies that it  exhibits ABA freedom.  

\verify2{
noABA volatile int n  
  moves_as isRead() ? N
                    : (newValue == this.n + 1 ? N : E)
  yields_as newValue >= this.n;
}{
class AtomicInc {

  noABA volatile int n  
    moves_as isRead() ? N
                      : (newValue == this.n + 1 ? N : E)
    yields_as newValue >= this.n;

  modifies this;
  ensures this.n == old(this.n) + 1;
  public void inc() {
    while (true) {
      int x = this.n;
      if (cas(this,n,x,x+1)) {
        break;
      }
      yield;
    }
  }
}
}

Moreover, it is sufficient to guarantee that there is no \kword{yield}
necessary between the read and \kword{cas} operations:

* The last loop iteration in \t{inc()} consists of a read of \t{n} into
\t{x}, followed by a successful \kword{cas} changing \t{this.n} from \t{x}
to \t{x+1}. Since \t{n} is ABA free, no other thread could have
written to \t{n} between the read and the successful \kword{cas}.  As
such, \tool considers the read operation to be a right-mover,
provided it is followed by a successful
\kword{cas}.  

<div class="d-flex justify-content-center">
|   |
| ----| -------------------------- 
| `R`{.anchor} | ` x = this.n;`
| `N`{.anchor} | ` successful-cas;`
</div> 

* On all earlier iterations, the read of \t{this.n} is followed by a failed
\kword{cas}, which is a both-mover.  Thus, any
call to \t{inc()} performs the following sequence of heap operations:

<div class="d-flex justify-content-center">
|   |
| ----| -------------------------- 
| `N`{.anchor} | ` x = this.n;`
| `B`{.anchor} | ` failed-cas;`
</div> 

The sequence [ \MN; \MB; \kword{yield} ]* \MR; \MN consists of
reducible sequences separated by yields and is P/C equivalent
equivalent.  Moreover, the reducible sequences are all no-ops, except
for the last, which has the heap effect of atomically incrementing
\t{this.n}, as required by \t{inc()}'s specification.

This more precise \kword{cas}-based reasoning can be very useful for verifying the correctness
of many non-blocking
algorithms. It involves verifying that \kword{noABA} fields are free from
ABA problems and treating reads from them differently, depending
on whether or not each read is followed by a successful \kword{cas}
operation. 



### Object Invariants

\tool supports
object invariants.  For example, to express that \t{Node}s in
a linked list must be ordered by their \t{item}s, we can add the
following invariant to our \t{Node} class from our stack example:

\verify2{
invariant this.next != null  
          ==> this.item <= this.next.item;	
}{
class Node {
  int item  moves_as isLocal(this) ? B 
                                   : (isRead() ? B : E);
  Node next moves_as isLocal(this) ? B 
                                   : (isRead() ? B : E);

  invariant this.next != null  ==>  this.item <= this.next.item;

  requires item <= next.item;
  public Node(int item, Node next) {
    this.item = item;
    this.next = next;
  }
}
}

\tool assumes all object invariants hold at the start of each P/C equivalent
method and immediately after each \kword{yield} operation, and it
verifies that the invariants hold at the end of each P/C equivalent method and
immediately before each \kword{yield} operation.


### Loop Termination

\tool requires that that any reducible 
sequence reaching its "commit" point must terminate.
As such, \tool verifies that any thread entering the "left-matching" (or "post-commit")
phase of a reducible block reaches a \kword{yield} point, and it rejects any program
that, when in the left-matching phase, blocks indefinitely (e.g., due to an
\t{acquire}) or loops indefinitely.  

For example, the following loop cannot appear between a non-mover operation and the next
\kword{yield}, since \tool does not verify loop termination without some additional help
from the programmer.

\buggy2{
for (int i = 0; i < 10; i = i + 1) {
  // ...
}
}{
class DecreasingLoop {
  
  volatile int value moves_as N;

  public void looping() {
    this.value = 0;   // non-mover!
    for (int i = 0; i < 10; i = i + 1) {
      // ...
    }
  }
}
}

In cases where a loop like this does indeed terminate, the programmer 
may supply a termination metric with a \kword{decreases} annotation
to provide a non-negative integer expression that decreases in
value on each loop iteration.  

\verify2{
for (int i = 0; i < 10; i = i + 1) 
  decreases 10 - i;
{
  // ...
}
}{
class DecreasingLoop {
  
  volatile int value moves_as N;

  public void looping() {
    this.value = 0;   // non-mover!
    for (int i = 0; i < 10; i = i + 1) 
      decreases 10 - i;
    {
      // ...
    }
  }
}
}

This is quite similar to how
[Dafny](https://rise4fun.com/Dafny/tutorial) treats loops.


### Non-Atomic Method Specifications

A public method containing no \kword{yield}s always has atomic behavior.
That behavior can be specified with standard \kword{requires},
\kword{modifies}, and \kword{ensures} annotations, as illustrated by our \t{Stack}'s \t{push()} method:


\verify2{
modifies this;
ensures this.head.next == old(this.head);
ensures this.head.item == item;
public void push(int item) {
  acquire(this);
  Node node = new Node(item, this.head);
  this.head = node; 
  release(this);
}
}{
$/examples/Stack.anchor
}

A \kword{public} method containing \kword{yield}s may also exhibit atomic behavior
if it never executes more than one \kword{yield}-free code region with
visible side effects.  The \t{pop()} method has this property.  In this case,
the specification captures the behavior of the one region with side effects:

\verify2{
modifies this;
ensures old(this.head) != null;
ensures $result == old(this.head.item); 
ensures this.head == old(this.head.next);
public int pop() {
  acquire(this);
  while (this.head == null) 
    invariant holds(this);
  {
    release(this);
    yield;
    acquire(this);
  }
  int value = this.head.item;
  this.head = this.head.next;
  release(this);
  return value;
}
}{
$/examples/Stack.anchor
}

The behavior of \kword{public} methods with non-atomic behavior can be
specified via a sequence of blocks containing \kword{modifies} and
\kword{ensures} clauses.  For example, the `incTwice` method in
our `AtomicIntClient` class can be specificed as follows

\verify2{
{
  modifies counter;
  ensures counter.n == old(counter.n) + 1;
}
yield;
{
  modifies counter;
  ensures counter.n == old(counter.n) + 1;
}
public void incTwice(AtomicInc counter) {
  int n = counter.inc();
  yield;
  assert counter.inc() >= n;
}
}{
  class AtomicInc {

  int n  moves_as holds(this) 
                  ? isRead() ? B 
                             : newValue == this.n + 1 ? B : E
                  : E
         yields_as newValue >= this.n;
         
  modifies this;
  ensures this.n == old(this.n) + 1;
  ensures $result == this.n;
  int inc() {
    synchronized(this) {
      this.n = this.n + 1;
      return this.n;
    }
  }
}

class AtomicIntClient {
  
  {
    modifies counter;
    ensures counter.n == old(counter.n) + 1;
  }
  yield;
  {
    modifies counter;
    ensures counter.n == old(counter.n) + 1;
  }
  public void incTwice(AtomicInc counter) {
    int n = counter.inc();
    yield;
    assert counter.inc() >= n;
  }
}
}

We include the \kword{yield} keyword in the specification to reinforce
that interference may occur at those intermediate points, and that the 
heap state at those points may be exposed to other threads.

The \t{add} method for a sorted linked list implemented with
hand-over-hand locking is similarly non-atomic and be specified as a 
sequence of three atomic blocks that refer to an
additional specification variable \t{ptr}.  The first initializes
\t{ptr} to the head of the list; the second (which may be iterated any
number of times) moves \t{ptr} one node further down the list,
performing the appropriate synchronization, until the insertion point
is found; and the third inserts a new node at that location.

\verify2{
{
  Node pred;
  {
    // start at head
    ensures pred == this.head && holds(pred);
  }
  yield;
  {
    // step down list, releasing old pred, and
    // acquiring new pred
    ensures old(holds(pred));
    ensures old(pred.next.item) < item;
    ensures pred == old(pred.next);
    ensures !holds(old(pred)) && holds(pred);
  }*
    yield;
  {
    // return false if already there.
    // return true and create new node at pred.next if not.
    modifies pred;
    ensures old(holds(pred)) && !holds(pred);
    ensures old(pred.next.item) >= item;
    ensures old(pred.next.item) == item ==> !$result;
    ensures old(pred.next.item) > item  
              ==> $result
                && pred.next.item == item 
                && pred.next.next == old(pred.next);
  }
}
public boolean add(int item) { 
  ...
}
}{
$/examples/HandOverHandLocking.anchor
}

\tool verifies that method bodies conform to their specifications a
simulation check that matches the execution of a yield-free region
to a corresponding step taken in the specification.

Using this feature comes with some caveats.  Most importantly,
\tool doesn't presently properly handle this type of specification 
for methods that may exit before reaching the end of the sequence.
\tool encodes a multi-block specification as an NFA and simulates
steps in the automata for each \kword{yield}-free region.  Debugging
problems when the simulation fails can be a bit tricky.  We expose the
the currents state of the NFA in the heap diagrams with special variables
`$spec$0`, `$spec$1`, etc. that capture the initial state, the state after
the first specification block is matched, and so on.  You can use those variables
to see where the simulation fails.


## Limitations

While we have tried to stick as close to Java as we could, there are 
some missing features and other limitations.  None of these are insurmountable,
but there was only so much we could do in our first \tool prototype...

Some of the missing Java features in subtyping, inheritance, and generics.
We also only have \t{int} and \t{boolean} primitives types, arrays may
only have one-dimension to make type checking and verification simpler,
there is no analog of packages or imports,
and some control structures (like \t{switch} statements) are missing.
\tool also does not support the pre/post `++` and `--` operators.
Since we currently inline method calls in \kword{public} methods, \tool
doesn't support recursion.

Your best bet for understanding what is presently supported is to look through
our many examples, which illustrate pretty much everything \tool can do.

You you encounter unusual behavior, missing features, misleading errors, etc. please let us know!

