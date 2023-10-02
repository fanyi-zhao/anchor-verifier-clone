---
title: 'Anchor Error Messages'
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

\tool checks some fairly complex, subtle properties.  While we have tried to ensure
that the error messages convery enough information to diagnose their cause, they do take
some time to get used to.  We provide some examples of errors below to illustrate what
they mean and how to approach fixing them.

### Validity Errors

Validity errors occur when a synchronization specificatino permits two access to 
commute in a way that might change program state.

Here is a declaration with a validity violation.  The field `value` can be updated
to any value until it becomes -1.  At that point, it becomes readonly.
The specification indicates that all reads and writes are initially non-movers until `value` does
become -1.  At that point, only reads are allowed and are both-movers.

\buggySnip{
  volatile int value 
      moves_as this.value != -1 ? N : (isRead() ? B : E);
}

Verifying this code identifies a validity problem, and \tool shows a pair of steps by different threads
that commute according to the specification but that change program behavior when they do.  The key is to 
identify those steps and strengthen the specification to prevent them from commuting.

In thise case, a read of -1 can left-commute 
past a write to the field.  However, this is problematic since the field's value might not be -1 before the write occurs, meaning the read 
will then see a different value.
We can rule out the problematic case by permitting reads of -1 to right-commute but not left-commute:

\verifySnip{
  volatile int value 
      moves_as this.value != -1 ? N : (isRead() ? R : E);
}


### Stability Errors

Stability errors occur when writing to one memory location may change a different
thread's permission to access a different location in a way that violates 
\tool's reduction reasoning.

Synchroniation specification must be stable in that the permission to read or write
a field is either invariant over interleaved writes, or at least changd in a way 
that does not invalidate \tool's reduction-based reasoning.  

Here is a case where stability doesn't hold.

\buggy{
class Example {
  volatile int m  moves_as N;
  int x           moves_as this.m == tid ? B : E;
}
}

The error reports identifies several steps that lead to instability.  The solution
is to strengthen the requirements on when the offending memory location may be
modified by other threads.

In this case, we change the specification so that a thread can only change `m` if
`m` is currently an invalid `tid` (`Tid.nul`) and the new value is the current
threads `tid`.  Thus, `m` never becomes the id of a different thread that may
try to access `x` concurrently.

\verify{
class Example {
  volatile int m  
    moves_as isRead() 
           ? N 
           : (this.m == Tid.null && newValue == tid ? N : E)
    yields_as this.m == tid ==> newValue == tid;

  int x moves_as this.m == tid ?  B : E;
}
}

(In this case, we also need to add a \kword{yields_as} annotation to indicate
tha other threads can't "steal" \t{this.m} from us.)

### Reduction Error

Reduction errors are most often caused by sequences of steps that do not
match our reducible pattern:

\buggy{
class Example {
  int value moves_as holds(this) ? B : E;

  public void f() {
    acquire(this);
    this.value = 1;
    release(this);
    acquire(this);
    this.value = 2;
    release(this);
  }
}
}

The fix is to change to:

1. insert a \kword{yield} if non-atomic behavior is desired;
2. change the synchronization specifications so accesses can commute as needed; or
3. change the synchronization operations in the code to eliminate the interference point.

In this case, either (1) or (3) is the likely best option:

\verify2{
  public void f() {
    acquire(this);
    this.value = 1;
    release(this);
    yield;
    acquire(this);
    this.value = 2;
    release(this);
  }
}{
class Example {
  int value moves_as holds(this) ? B : E;

  public void f() {
    acquire(this);
    this.value = 1;
    release(this);
    yield;
    acquire(this);
    this.value = 2;
    release(this);
  }
}
}

or:

\verify2{
  public void f() {
    acquire(this);
    this.value = 1;
    this.value = 2;
    release(this);
  }
}{
class Example {
  int value moves_as holds(this) ? B : E;

  public void f() {
    acquire(this);
    this.value = 1;
    this.value = 2;
    release(this);
  }
}
}


### Loop Reduction Error

Another type of reduction error occurs because \tool requires that the phase --- either "pre-commit" (matching right movers) or
"post-commit" (matching left movers) --- be invariant at loop heads.  Thus the following code fails, since we are matching right movers when we first encounter the loop but are maching left movers on the back edge.

\buggy{
class Example {
  public void f() {
    while (true) {
      acquire(this);
      release(this);
    }
  }
}
}

If there is not other underlying issue, fixing this typically requires restructuring the loop and/or adding \kword{yield}:

\verify{
class Example {
  public void f() {
    while (true) {
      acquire(this);
      release(this);
      yield;
    }
  }  
}
}


### Volatile Errors

Any field that may be a left, right, or non-mover may be prone
to data races.  

\buggy{
class Example {
  int value moves_as N;
}
}

As such, it must be declared volatile
to ensure sequentially consistent behavior.  

\verify{
class Example {
  int value moves_as N;
}
}

Array elements cannot
be assigned those commutivities.  This is a consequence of our Java
not having an easy way to make array elements be volatile.

### Specification Error

#### Method returns before completing actions in spec

This happens when \tool cannot matching the execution of
atomic code blocks to steps of the specification.  Here is a
simple example:

\buggy{
class Example {
  
  volatile int f moves_as N;
   
  modifies this;
  ensures this.f == 1;
  public void f() {
    this.f = 2;
  }  
}
}

It can be fixed by ensuring the update to \t{this.f} in the
code matches the space.

For multi-step specification, \tool encodes the specification as an NFA and simulates
steps in the automata for each \kword{yield}-free region.  Debugging
problems when the simulation fails can be a bit tricky.  

We expose the the currents state of the NFA in the heap diagrams with special variables
`$spec$0`, `$spec$1`, etc. that capture the initial state, the state after
the first specification block is matched, and so on.  You can use those variables
to see which states the simulation may be in, which often provides some insight
into why the error occurs.  For example, in the following, inspecting the pre-state 
and post-state for the first \tkword{yield} shows that \tool matched the first step 
of the spec to the first block of code (since `$spec$0`, the initial state became
false and `$spec$1` became true).  Inspecting the information for the return
shows, however, that the second step failed to be matched (since `spec$1` became false and `$spec$2`, the 
accepting state, failed to become true).

\buggy{
class Example {
  
  volatile int f moves_as N;
   
  {
    modifies this;
    ensures this.f == 1;
  } 
  yield;
  {
    modifies this;
    ensures this.f == 2;
  } 
  public void f() {
    this.f = 1;
    yield;
    this.f = 3;
  }  
}
}

Again, the fix is to change either the code or the spec so that they match.

Keep in mind that side-effect free code blocks can be ignored during simulation.
It's only the ones with side effects that must match specification steps.

Also keep in mind that you should not return early from methods with
multi-step specs.  That is a current limitation of our translation.


### Requires Error

Requires clauses may refer to heap locations but all accesses
must be right-movers to ensure that they capture the state 
visible to the method as it begins executing.  Otherwise,
when performing reduction, there could
be steps interleaved from other threads between when
the \kword{requires} annotations are established and
when the code begins executing.  This requirement precludes
code like the following:

\buggy{
class Example {
  
  volatile int f moves_as write_guarded_by this;
        // or isRead() ? holds(this) ? B : N
        //             : holds(this) ? N : E
    
  requires this.f == 0;
  public void f() {
  }  
}
}

The solution is typically to strenghten the specification or
add additional requires annotations.  In this case, we could
require the lock to be held:

\verify2{
requires holds(this);
requires this.f == 0;
public void f()
}{
class Example {
  
  volatile int f moves_as write_guarded_by this;
        // or isRead() ? holds(this) ? B : N
        //             : holds(this) ? N : E
    
  requires holds(this);
  requires this.f == 0;
  public void f() {
  }  
}
}


### YieldsAs Errors

The \kword{yields_as} annotation captures all possible values that could
be stored in a memory location during a \kword{yield} by thread \kword{tid}.

Any \kword{yields} as annotation must be valid, reflexive, and transitive:

* It is valid if it captures *all* possible updates by other threads.
* It is reflextive if it permits the location to remain unchanged.
* It is transitive if, given all the \kword{yields_as} annotations for a program,
two \kword{yield}s in a row do not enable any additional values to be stored
in the location.

The default \kword{yields_as} annotation is that the location remains unchanged
if thread \kword{tid} has right-mover read access to it, meaning the read could occur before or after any steps taken by other threads at the yield.

#### yields_as clause is not valid / reflexive / transitive

These errors occur when one of the three necessary properties is violated.  Here's an example that breaks all three:

\buggy{
class YieldsAsBroken {
  volatile int value 
    moves_as isRead() ? N 
                      : (newValue >= this.value ? N : E)
    yields_as this.value != newValue;
}
}

The \kword{yields_as} doesn't admit the case when \t{newValue == this.value}, so it is neither valid (since the synchronization specification permits that) nor reflexive.  It is not transitive, because the \kword{yields_as} permits the value to change to a new value by one \kword{yield} but then change back to the original value in a second \kword{yield} immediately following the first.  We can fix this by simply change the code to the following:

\verify{
class YieldsAsOK {
  volatile int value 
    moves_as isRead() ? N 
                      : (newValue >= this.value ? N : E)
    yields_as this.value <= newValue;
  }
}

#### Field is not ABA-free

\tool verifies that such a field exhibits
ABA freedom, namely that that the field is never changed from a value
$A$ to $B$ and then back to $A$ again, using the \kword{yields_as}
annotation.  For example, in the following code snippet the \t{value}
field is declared \kword{noABA}, but it does not include a \kword{yields_as}
annotation strong enough to guarantee that it is indeed ABA-free.

\buggy{
class BadNoABA {
  noABA int value  
    moves_as holds(this) 
             ? isRead() ? B 
                          : newValue == this.value + 1 ? B : E
             : E;
} 
}

The following \kword{yields_as} annotation fixes that, because 
if \t{value} is currently $A$ and another thread updates it
to a new and distinct value $B$, it must be that $B > A$.  No thread
could change \t{value} back to $A$ without violating the field's
\kword{yields_as} specification since it is not the case that $B < A$.

\verify{
class NoABA {
  noABA int value
    moves_as holds(this) 
             ? isRead() ? B 
                        : newValue == this.value + 1 ? B : E
             : E;
}
}

### Loop Termination Errors

An atomic block that reaches it's commit point must reach its end.
This requires that \tool be able to verify that
loops appearing in the post-commit phase do indeed finish.
You may see several different errors related to this.

#### Potentially infinite loop head cannot be in post-commit phase

This error means that \tool did not find a \kword{decreasing} annotation
ensuring that a post-commit loop terminates, as in the following:

\buggy{
class PostCommitLoop {
  volatile int value moves_as N;
  
  public void f() {
    
    // in pre-commit phase
    
    this.value = 1;  
    // in post-commit phase
    
    for (int i = 0; i < 10; i = i + 1) {
      // ...
    }
  }
}
}

Even though termination is obvious to us, \tool still requires it
to be documented:

\verify2{
for (int i = 0; i < 10; i = i + 1) 
  decreases 10 - i;
{
    // ...
}
}{
class PostCommitLoop {
  volatile int value moves_as N;
  
  public void f() {
    
    // in pre-commit phase
    
    this.value = 1;  
    // in post-commit phase
    
    for (int i = 0; i < 10; i = i + 1) 
      decreases 10 - i;
    {
      // ...
    }
  }
}
}

#### Loop may not terminate

This error is caused by a \kword{decreasing} annotation whose expression 
may increase rather than decrease, as in the following broken version of the above:

\buggy2{
for (int i = 0; i < 10; i = i + 1) 
  decreases i;
{
    // ...
}
}{
class PostCommitLoop {
  volatile int value moves_as N;
  
  public void f() {
    
    // in pre-commit phase
    
    this.value = 1;  
    // in post-commit phase
    
    for (int i = 0; i < 10; i = i + 1) 
      decreases i;
    {
      // ...
    }
  }
}
}

#### Decreasing expression not properly bounded by 0

This error is caused by a \kword{decreasing} annotation whose expression 
decreases but may also become negative:

\buggy2{
int i;
while (i < 10)
  decreases i;
{
    i = i - 1;
}
}{
class UnboundedDecreasingLoop {
  public void f() {
    int i;
    while (i < 10)
    decreases i;
    {
        i = i - 1;
    }
  }
}
}
