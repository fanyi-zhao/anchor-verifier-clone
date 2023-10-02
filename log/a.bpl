                                                                                                    
 /*                                                                                                 
                                                                                                    
 /tmp/tmpizv5m2g1/b.anchor:                                                                         
                                                                                                    
 AST:                                                                                               
                                                                                                    
                                                                                                    
                                                                                                    
    class Node {                                                                                    
       int item isLocal(this, tid)                                                                  
       ? B                                                                                          
       : isRead ? B : E                                                                             
                                                                                                    
       Node next isLocal(this, tid)                                                                 
       ? B                                                                                          
       : isRead ? B : E                                                                             
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
      void init(int item,Node next) {                                                               
        assume this.item == 0;                                                                      
        assume this.next == Node.null;                                                              
        {                                                                                           
          this.item := item;                                                                        
          this.next := next;                                                                        
          // return;                                                                                
        }                                                                                           
      }                                                                                             
                                                                                                    
    }                                                                                               
    class Stack {                                                                                   
       Node head holds(this, tid) ? B : E                                                           
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
      void init() {                                                                                 
        assume this.head == Node.null;                                                              
        {                                                                                           
          // return;                                                                                
        }                                                                                           
      }                                                                                             
                                                                                                    
                                                                                                    
                                                                                                    
      {                                                                                             
        modifies this;                                                                              
        ensures this.head.next == old(this.head);                                                   
        ensures this.head.item == item;                                                             
      }                                                                                             
      public void push(int item) {                                                                  
        acquire(this);                                                                              
        Node node;                                                                                  
        node = new Node();                                                                          
        Node tmp1;                                                                                  
        tmp1 := this.head;                                                                          
        node.init(item,tmp1)                                                                        
        this.head := node;                                                                          
        release(this);                                                                              
        // return;                                                                                  
      }                                                                                             
                                                                                                    
                                                                                                    
                                                                                                    
      {                                                                                             
        modifies this;                                                                              
        ensures old(this.head) != Node.null;                                                        
        ensures $result == old(this.head.item);                                                     
        ensures this.head == old(this.head.next);                                                   
      }                                                                                             
      public int pop() {                                                                            
        acquire(this);                                                                              
        while (true)                                                                                
          invariant holds(this, tid);                                                               
          {                                                                                         
          boolean tmp2;                                                                             
          Node tmp3;                                                                                
          tmp3 := this.head;                                                                        
          tmp2 = tmp3 == Node.null;                                                                 
          if (!tmp2) break; else {                                                                  
                                                                                                    
          }                                                                                         
          {                                                                                         
            release(this);                                                                          
            yield;                                                                                  
            acquire(this);                                                                          
          }                                                                                         
        }                                                                                           
        int value;                                                                                  
        Node tmp4;                                                                                  
        tmp4 := this.head;                                                                          
        value := tmp4.item;                                                                         
        Node tmp5;                                                                                  
        Node tmp6;                                                                                  
        tmp6 := this.head;                                                                          
        tmp5 := tmp6.next;                                                                          
        this.head := tmp5;                                                                          
        release(this);                                                                              
         return value;                                                                              
        // return -1;                                                                               
      }                                                                                             
                                                                                                    
    }                                                                                               
                                                                                                    
                                                                                                    
                                                                                                    
 Explicit:                                                                                          
                                                                                                    
                                                                                                    
                                                                                                    
    class Node {                                                                                    
       int item isLocal(this, tid)                                                                  
       ? B                                                                                          
       : isRead ? B : E                                                                             
                                                                                                    
       Node next isLocal(this, tid)                                                                 
       ? B                                                                                          
       : isRead ? B : E                                                                             
                                                                                                    
       Tid _lock isLocal(this, tid)                                                                 
       ? isRead                                                                                     
         ? B                                                                                        
         : newValue == tid || newValue == Tid.null ? B : E                                          
       : isRead                                                                                     
         ? this._lock == tid ? R : E                                                                
         : this._lock == Tid.null && newValue == tid                                                
           ? R                                                                                      
           : this._lock == tid && newValue == Tid.null ? L : E !                                    
        yields_as this._lock == tid == (newValue == tid);                                           
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
      void init(int item,Node next) {                                                               
        assume this.item == 0;                                                                      
        assume this.next == Node.null;                                                              
        {                                                                                           
          this.item := item;                                                                        
          this.next := next;                                                                        
          {                                                                                         
            // return;                                                                              
          }                                                                                         
        }                                                                                           
      }                                                                                             
                                                                                                    
    }                                                                                               
    class Stack {                                                                                   
       Node head holds(this, tid) ? B : E                                                           
                                                                                                    
       Tid _lock isLocal(this, tid)                                                                 
       ? isRead                                                                                     
         ? B                                                                                        
         : newValue == tid || newValue == Tid.null ? B : E                                          
       : isRead                                                                                     
         ? this._lock == tid ? R : E                                                                
         : this._lock == Tid.null && newValue == tid                                                
           ? R                                                                                      
           : this._lock == tid && newValue == Tid.null ? L : E !                                    
        yields_as this._lock == tid == (newValue == tid);                                           
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
      void init() {                                                                                 
        assume this.head == Node.null;                                                              
        {                                                                                           
          {                                                                                         
            // return;                                                                              
          }                                                                                         
        }                                                                                           
      }                                                                                             
                                                                                                    
                                                                                                    
                                                                                                    
      {                                                                                             
        modifies this;                                                                              
        ensures this.head.next == old(this.head);                                                   
        ensures this.head.item == item;                                                             
      }                                                                                             
      public void push(int item) {                                                                  
        acquire(this);                                                                              
        Node node;                                                                                  
        node = new Node();                                                                          
        Node tmp1;                                                                                  
        tmp1 := this.head;                                                                          
        node.init(item,tmp1)                                                                        
        this.head := node;                                                                          
        release(this);                                                                              
        {                                                                                           
          // return;                                                                                
        }                                                                                           
      }                                                                                             
                                                                                                    
                                                                                                    
                                                                                                    
      {                                                                                             
        modifies this;                                                                              
        ensures old(this.head) != Node.null;                                                        
        ensures $result == old(this.head.item);                                                     
        ensures this.head == old(this.head.next);                                                   
      }                                                                                             
      public int pop() {                                                                            
        acquire(this);                                                                              
        while (true)                                                                                
          invariant holds(this, tid);                                                               
          {                                                                                         
          boolean tmp2;                                                                             
          Node tmp3;                                                                                
          tmp3 := this.head;                                                                        
          tmp2 = tmp3 == Node.null;                                                                 
          if (!tmp2) {                                                                              
            break;                                                                                  
          } else {                                                                                  
                                                                                                    
          }                                                                                         
          {                                                                                         
            release(this);                                                                          
            yield;                                                                                  
            acquire(this);                                                                          
          }                                                                                         
        }                                                                                           
        int value;                                                                                  
        Node tmp4;                                                                                  
        tmp4 := this.head;                                                                          
        value := tmp4.item;                                                                         
        Node tmp5;                                                                                  
        Node tmp6;                                                                                  
        tmp6 := this.head;                                                                          
        tmp5 := tmp6.next;                                                                          
        this.head := tmp5;                                                                          
        release(this);                                                                              
        {                                                                                           
           return value;                                                                            
        }                                                                                           
        {                                                                                           
          // return -1;                                                                             
        }                                                                                           
      }                                                                                             
                                                                                                    
    }                                                                                               
                                                                                                    
                                                                                                    
                                                                                                    
 Inlined:                                                                                           
                                                                                                    
                                                                                                    
                                                                                                    
    class Node {                                                                                    
       int item isLocal(this, tid)                                                                  
       ? B                                                                                          
       : isRead ? B : E                                                                             
                                                                                                    
       Node next isLocal(this, tid)                                                                 
       ? B                                                                                          
       : isRead ? B : E                                                                             
                                                                                                    
       Tid _lock isLocal(this, tid)                                                                 
       ? isRead                                                                                     
         ? B                                                                                        
         : newValue == tid || newValue == Tid.null ? B : E                                          
       : isRead                                                                                     
         ? this._lock == tid ? R : E                                                                
         : this._lock == Tid.null && newValue == tid                                                
           ? R                                                                                      
           : this._lock == tid && newValue == Tid.null ? L : E !                                    
        yields_as this._lock == tid == (newValue == tid);                                           
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
      void init(int item,Node next) {                                                               
        assume this.item == 0;                                                                      
        assume this.next == Node.null;                                                              
        {                                                                                           
          this.item := item;                                                                        
          this.next := next;                                                                        
          {                                                                                         
            // return;                                                                              
          }                                                                                         
        }                                                                                           
      }                                                                                             
                                                                                                    
    }                                                                                               
    class Stack {                                                                                   
       Node head holds(this, tid) ? B : E                                                           
                                                                                                    
       Tid _lock isLocal(this, tid)                                                                 
       ? isRead                                                                                     
         ? B                                                                                        
         : newValue == tid || newValue == Tid.null ? B : E                                          
       : isRead                                                                                     
         ? this._lock == tid ? R : E                                                                
         : this._lock == Tid.null && newValue == tid                                                
           ? R                                                                                      
           : this._lock == tid && newValue == Tid.null ? L : E !                                    
        yields_as this._lock == tid == (newValue == tid);                                           
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
      void init() {                                                                                 
        assume this.head == Node.null;                                                              
        {                                                                                           
          {                                                                                         
            // return;                                                                              
          }                                                                                         
        }                                                                                           
      }                                                                                             
                                                                                                    
                                                                                                    
                                                                                                    
      {                                                                                             
        modifies this;                                                                              
        ensures this.head.next == old(this.head);                                                   
        ensures this.head.item == item;                                                             
      }                                                                                             
      public void push(int item) {                                                                  
        acquire(this);                                                                              
        Node node;                                                                                  
        node = new Node();                                                                          
        Node tmp1;                                                                                  
        tmp1 := this.head;                                                                          
        {                                                                                           
          inlined node.init(item,tmp1);                                                             
          exit$1: {                                                                                 
            int item$1;                                                                             
            Node next$1;                                                                            
            Node this$1;                                                                            
            item$1 = item;                                                                          
            next$1 = tmp1;                                                                          
            this$1 = node;                                                                          
            {                                                                                       
              assume this$1.item == 0;                                                              
              assume this$1.next == Node.null;                                                      
              {                                                                                     
                this$1.item := item$1;                                                              
                this$1.next := next$1;                                                              
                {                                                                                   
                  break exit$1;                                                                     
                }                                                                                   
              }                                                                                     
            }                                                                                       
          }                                                                                         
          inlined return;                                                                           
        }                                                                                           
        this.head := node;                                                                          
        release(this);                                                                              
        {                                                                                           
          // return;                                                                                
        }                                                                                           
      }                                                                                             
                                                                                                    
                                                                                                    
                                                                                                    
      {                                                                                             
        modifies this;                                                                              
        ensures old(this.head) != Node.null;                                                        
        ensures $result == old(this.head.item);                                                     
        ensures this.head == old(this.head.next);                                                   
      }                                                                                             
      public int pop() {                                                                            
        acquire(this);                                                                              
        while (true)                                                                                
          invariant holds(this, tid);                                                               
          {                                                                                         
          boolean tmp2;                                                                             
          Node tmp3;                                                                                
          tmp3 := this.head;                                                                        
          tmp2 = tmp3 == Node.null;                                                                 
          if (!tmp2) {                                                                              
            break;                                                                                  
          } else {                                                                                  
                                                                                                    
          }                                                                                         
          {                                                                                         
            release(this);                                                                          
            yield;                                                                                  
            acquire(this);                                                                          
          }                                                                                         
        }                                                                                           
        int value;                                                                                  
        Node tmp4;                                                                                  
        tmp4 := this.head;                                                                          
        value := tmp4.item;                                                                         
        Node tmp5;                                                                                  
        Node tmp6;                                                                                  
        tmp6 := this.head;                                                                          
        tmp5 := tmp6.next;                                                                          
        this.head := tmp5;                                                                          
        release(this);                                                                              
        {                                                                                           
           return value;                                                                            
        }                                                                                           
        {                                                                                           
          // return -1;                                                                             
        }                                                                                           
      }                                                                                             
                                                                                                    
    }                                                                                               
                                                                                                    
                                                                                                    
                                                                                                    
 Prepared:                                                                                          
                                                                                                    
                                                                                                    
                                                                                                    
    class Node {                                                                                    
       int item isLocal(this, tid)                                                                  
       ? B                                                                                          
       : isRead ? B : E                                                                             
                                                                                                    
       Node next isLocal(this, tid)                                                                 
       ? B                                                                                          
       : isRead ? B : E                                                                             
                                                                                                    
       Tid _lock isLocal(this, tid)                                                                 
       ? isRead                                                                                     
         ? B                                                                                        
         : newValue == tid || newValue == Tid.null ? B : E                                          
       : isRead                                                                                     
         ? this._lock == tid ? R : E                                                                
         : this._lock == Tid.null && newValue == tid                                                
           ? R                                                                                      
           : this._lock == tid && newValue == Tid.null ? L : E !                                    
        yields_as this._lock == tid == (newValue == tid);                                           
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
      void init(int item,Node next) {                                                               
        assume this.item == 0;                                                                      
        assume this.next == Node.null;                                                              
        {                                                                                           
          this.item := item;                                                                        
          this.next := next;                                                                        
          {                                                                                         
            // return;                                                                              
          }                                                                                         
        }                                                                                           
      }                                                                                             
                                                                                                    
    }                                                                                               
    class Stack {                                                                                   
       Node head holds(this, tid) ? B : E                                                           
                                                                                                    
       Tid _lock isLocal(this, tid)                                                                 
       ? isRead                                                                                     
         ? B                                                                                        
         : newValue == tid || newValue == Tid.null ? B : E                                          
       : isRead                                                                                     
         ? this._lock == tid ? R : E                                                                
         : this._lock == Tid.null && newValue == tid                                                
           ? R                                                                                      
           : this._lock == tid && newValue == Tid.null ? L : E !                                    
        yields_as this._lock == tid == (newValue == tid);                                           
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
      void init() {                                                                                 
        assume this.head == Node.null;                                                              
        {                                                                                           
          {                                                                                         
            // return;                                                                              
          }                                                                                         
        }                                                                                           
      }                                                                                             
                                                                                                    
                                                                                                    
                                                                                                    
      {                                                                                             
        modifies this;                                                                              
        ensures this.head.next == old(this.head);                                                   
        ensures this.head.item == item;                                                             
      }                                                                                             
      public void push(int item) {                                                                  
        acquire(this);                                                                              
        Node node;                                                                                  
        node = new Node();                                                                          
        Node tmp1;                                                                                  
        tmp1 := this.head;                                                                          
        {                                                                                           
          inlined node.init(item,tmp1);                                                             
          exit$1: {                                                                                 
            int item$1;                                                                             
            Node next$1;                                                                            
            Node this$1;                                                                            
            item$1 = item;                                                                          
            next$1 = tmp1;                                                                          
            this$1 = node;                                                                          
            {                                                                                       
              assume this$1.item == 0;                                                              
              assume this$1.next == Node.null;                                                      
              {                                                                                     
                this$1.item := item$1;                                                              
                this$1.next := next$1;                                                              
                {                                                                                   
                  break exit$1;                                                                     
                }                                                                                   
              }                                                                                     
            }                                                                                       
          }                                                                                         
          inlined return;                                                                           
        }                                                                                           
        this.head := node;                                                                          
        release(this);                                                                              
        {                                                                                           
          // return;                                                                                
        }                                                                                           
      }                                                                                             
                                                                                                    
                                                                                                    
                                                                                                    
      {                                                                                             
        modifies this;                                                                              
        ensures old(this.head) != Node.null;                                                        
        ensures $result == old(this.head.item);                                                     
        ensures this.head == old(this.head.next);                                                   
      }                                                                                             
      public int pop() {                                                                            
        acquire(this);                                                                              
        while (true)                                                                                
          invariant holds(this, tid);                                                               
          {                                                                                         
          boolean tmp2;                                                                             
          Node tmp3;                                                                                
          tmp3 := this.head;                                                                        
          tmp2 = tmp3 == Node.null;                                                                 
          if (!tmp2) {                                                                              
            break;                                                                                  
          } else {                                                                                  
                                                                                                    
          }                                                                                         
          {                                                                                         
            release(this);                                                                          
            yield;                                                                                  
            acquire(this);                                                                          
          }                                                                                         
        }                                                                                           
        int value;                                                                                  
        Node tmp4;                                                                                  
        tmp4 := this.head;                                                                          
        value := tmp4.item;                                                                         
        Node tmp5;                                                                                  
        Node tmp6;                                                                                  
        tmp6 := this.head;                                                                          
        tmp5 := tmp6.next;                                                                          
        this.head := tmp5;                                                                          
        release(this);                                                                              
        {                                                                                           
           return value;                                                                            
        }                                                                                           
        {                                                                                           
          // return -1;                                                                             
        }                                                                                           
      }                                                                                             
                                                                                                    
    }                                                                                               
                                                                                                    
                                                                                                    
 */                                                                                                 
                                                                                                    
//// Background                                                                                     
                                                                                                    
                                                                                                    
 /*                                                                                                 
 * Tid                                                                                              
 */                                                                                                 
 type Tid = int;  // make int so you can iterate over Tids                                          
 const unique Tid.null: Tid;                                                                        
 axiom Tid.null == -1;                                                                              
                                                                                                    
 function {:inline} ValidTid(tid : Tid): bool {                                                     
  tid != Tid.null && tid >= 0                                                                       
 }                                                                                                  
                                                                                                    
 type{:datatype} State;                                                                             
 function{:constructor} NULL(): State;                                                              
 function{:constructor} FRESH(): State;                                                             
 function{:constructor} LOCAL(t: Tid): State;                                                       
 function{:constructor} SHARED(): State;                                                            
                                                                                                    
 function {:inline} isNull(state: State) : bool {                                                   
  state == NULL()                                                                                   
 }                                                                                                  
                                                                                                    
 function {:inline} isFresh(state: State) : bool {                                                  
  state == FRESH()                                                                                  
 }                                                                                                  
                                                                                                    
 function {:inline} isShared(state: State) : bool {                                                 
  state == SHARED()                                                                                 
 }                                                                                                  
                                                                                                    
 function {:inline} isLocal(state: State, t: Tid) : bool {                                          
  state == LOCAL(t)                                                                                 
 }                                                                                                  
                                                                                                    
 function {:inline} isLocalAssignable(state: State, t: Tid) : bool {                                
  state == LOCAL(t) || state == SHARED() || state == NULL()                                         
 }                                                                                                  
                                                                                                    
 function {:inline} isSharedAssignable(state: State) : bool {                                       
  state == SHARED() || state == NULL()                                                              
 }                                                                                                  
                                                                                                    
 function {:inline} isAccessible(state: State, t: Tid) : bool {                                     
  state == LOCAL(t) || state == SHARED()                                                            
 }                                                                                                  
                                                                                                    
 function {:inline} isAllocated(state: State) : bool {                                              
  !isFresh(state) && !isNull(state)                                                                 
 }                                                                                                  
                                                                                                    
                                                                                                    
 function MOD(x:int, y:int): int;                                                                   
                                                                                                    
                                                                                                    
 /*                                                                                                 
 * For triggers                                                                                     
 */                                                                                                 
 function {:inline false} _trigger(i: int): bool {  true  }                                         
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 type Phase;                                                                                        
 const unique PreCommit : Phase;                                                                    
 const unique PostCommit : Phase;                                                                   
 const unique PhaseError : Phase;                                                                   
                                                                                                    
 function {:inline} transition(p: Phase, m: Mover): Phase {                                         
  if (m == _B) then                                                                                 
   p                                                                                                
  else if (m == _R) then                                                                            
   if (p == PreCommit) then                                                                         
    PreCommit                                                                                       
   else                                                                                             
    PhaseError                                                                                      
  else if (m == _L) then                                                                            
   if (p == PostCommit) then                                                                        
    PostCommit                                                                                      
   else if (p == PreCommit) then                                                                    
    PostCommit                                                                                      
   else                                                                                             
    PhaseError                                                                                      
  else if (m == _N) then                                                                            
   if (p == PreCommit) then                                                                         
    PostCommit                                                                                      
   else                                                                                             
    PhaseError                                                                                      
  else                                                                                              
   PhaseError // m == E or m == I                                                                   
 }                                                                                                  
                                                                                                    
                                                                                                    
 type Mover;                                                                                        
 const unique _B : Mover;                                                                           
 const unique _R : Mover;                                                                           
 const unique _L : Mover;                                                                           
 const unique _N : Mover;                                                                           
 const unique _E : Mover;                                                                           
                                                                                                    
 axiom (forall m : Mover :: m == _B || m == _R || m == _L || m == _N || m == _E);                   
                                                                                                    
 function {:inline} leq(m1: Mover, m2: Mover) : bool {                                              
  if (m1 == _B) then                                                                                
   true                                                                                             
  else if (m1 == _R) then                                                                           
   m2 == _R || m2 == _N || m2 == _E                                                                 
  else if (m1 == _L) then                                                                           
   m2 == _L || m2 == _N || m2 == _E                                                                 
  else if (m1 == _N) then                                                                           
   m2 == _N || m2 == _E                                                                             
  else if (m1 == _E) then                                                                           
   m2 == _E                                                                                         
  else                                                                                              
   false // should never happen...                                                                  
 }                                                                                                  
                                                                                                    
 function {:inline} lt(m1: Mover, m2: Mover) : bool { m1 != m2 && leq(m1, m2) }                     
                                                                                                    
 function {:inline} isError(m : Mover) : bool {                                                     
  m == _E                                                                                           
 }                                                                                                  
                                                                                                    
 function {:inline} eqOrError(m : Mover, n : Mover) : bool {                                        
  m == n || m == _E                                                                                 
 }                                                                                                  
                                                                                                    
 type{:datatype} MoverPath;                                                                         
 function{:constructor} moverPath(m:Mover, p:int):MoverPath;                                        
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
//// axioms                                                                                         
                                                                                                    
                                                                                                    
//// classes                                                                                        
                                                                                                    
                                                                                                    
/*** Class Decl Node ***/                                                                           
                                                                                                    
type Node;                                                                                          
const unique Node.null: Node;                                                                       
var Node._state: [Node]State;                                                                       
                                                                                                    
                                                                                                    
/////                                                                                               
                                                                                                    
var Node.item: [Node]int;                                                                           
                                                                                                    
function {:inline} ReadEval.Node.item(tid: Tid,this : Node,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid) returns (MoverPath) {
 (var isRead := true;                                                                               
 (var newValue := 0;                                                                                
 if (isLocal(Node._state[this], tid)) then                                                          
  moverPath(_B, 1)                                                                                  
 else                                                                                               
  if (isRead) then                                                                                  
   moverPath(_B, 2)                                                                                 
  else                                                                                              
   moverPath(_E, 0)                                                                                 
 )                                                                                                  
 )                                                                                                  
}                                                                                                   
                                                                                                    
function {:inline} WriteEval.Node.item(tid: Tid,this : Node,newValue: int,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid) returns (MoverPath) {
 (var isRead := false;                                                                              
 if (isLocal(Node._state[this], tid)) then                                                          
  moverPath(_B, 1)                                                                                  
 else                                                                                               
  if (isRead) then                                                                                  
   moverPath(_B, 2)                                                                                 
  else                                                                                              
   moverPath(_E, 0)                                                                                 
 )                                                                                                  
}                                                                                                   
                                                                                                    
/////                                                                                               
                                                                                                    
/////                                                                                               
                                                                                                    
var Node.next: [Node]Node;                                                                          
                                                                                                    
function {:inline} ReadEval.Node.next(tid: Tid,this : Node,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid) returns (MoverPath) {
 (var isRead := true;                                                                               
 (var newValue := Node.null;                                                                        
 if (isLocal(Node._state[this], tid)) then                                                          
  moverPath(_B, 1)                                                                                  
 else                                                                                               
  if (isRead) then                                                                                  
   moverPath(_B, 2)                                                                                 
  else                                                                                              
   moverPath(_E, 0)                                                                                 
 )                                                                                                  
 )                                                                                                  
}                                                                                                   
                                                                                                    
function {:inline} WriteEval.Node.next(tid: Tid,this : Node,newValue: Node,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid) returns (MoverPath) {
 (var isRead := false;                                                                              
 if (isLocal(Node._state[this], tid)) then                                                          
  moverPath(_B, 1)                                                                                  
 else                                                                                               
  if (isRead) then                                                                                  
   moverPath(_B, 2)                                                                                 
  else                                                                                              
   moverPath(_E, 0)                                                                                 
 )                                                                                                  
}                                                                                                   
                                                                                                    
/////                                                                                               
                                                                                                    
/////                                                                                               
                                                                                                    
var Node._lock: [Node]Tid;                                                                          
                                                                                                    
function {:inline} ReadEval.Node._lock(tid: Tid,this : Node,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid) returns (MoverPath) {
 (var isRead := true;                                                                               
 (var newValue := Tid.null;                                                                         
 if (isLocal(Node._state[this], tid)) then                                                          
  if (isRead) then                                                                                  
   moverPath(_B, 3)                                                                                 
  else                                                                                              
   if (((newValue==tid)||(newValue==Tid.null))) then                                                
    moverPath(_B, 5)                                                                                
   else                                                                                             
    moverPath(_E, 1)                                                                                
 else                                                                                               
  if (isRead) then                                                                                  
   if ((Node._lock[this]==tid)) then                                                                
    moverPath(_R, 6)                                                                                
   else                                                                                             
    moverPath(_E, 2)                                                                                
  else                                                                                              
   if (((Node._lock[this]==Tid.null)&&(newValue==tid))) then                                        
    moverPath(_R, 4)                                                                                
   else                                                                                             
    if (((Node._lock[this]==tid)&&(newValue==Tid.null))) then                                       
     moverPath(_L, 8)                                                                               
    else                                                                                            
     moverPath(_E, 0)                                                                               
 )                                                                                                  
 )                                                                                                  
}                                                                                                   
                                                                                                    
function {:inline} WriteEval.Node._lock(tid: Tid,this : Node,newValue: Tid,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid) returns (MoverPath) {
 (var isRead := false;                                                                              
 if (isLocal(Node._state[this], tid)) then                                                          
  if (isRead) then                                                                                  
   moverPath(_B, 3)                                                                                 
  else                                                                                              
   if (((newValue==tid)||(newValue==Tid.null))) then                                                
    moverPath(_B, 5)                                                                                
   else                                                                                             
    moverPath(_E, 1)                                                                                
 else                                                                                               
  if (isRead) then                                                                                  
   if ((Node._lock[this]==tid)) then                                                                
    moverPath(_R, 6)                                                                                
   else                                                                                             
    moverPath(_E, 2)                                                                                
  else                                                                                              
   if (((Node._lock[this]==Tid.null)&&(newValue==tid))) then                                        
    moverPath(_R, 4)                                                                                
   else                                                                                             
    if (((Node._lock[this]==tid)&&(newValue==Tid.null))) then                                       
     moverPath(_L, 8)                                                                               
    else                                                                                            
     moverPath(_E, 0)                                                                               
 )                                                                                                  
}                                                                                                   
                                                                                                    
/////                                                                                               
                                                                                                    
                                                                                                    
/////                                                                                               
                                                                                                    
/////                                                                                               
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
/*** Class Decl Stack ***/                                                                          
                                                                                                    
type Stack;                                                                                         
const unique Stack.null: Stack;                                                                     
var Stack._state: [Stack]State;                                                                     
                                                                                                    
                                                                                                    
/////                                                                                               
                                                                                                    
var Stack.head: [Stack]Node;                                                                        
                                                                                                    
function {:inline} ReadEval.Stack.head(tid: Tid,this : Stack,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid) returns (MoverPath) {
 (var isRead := true;                                                                               
 (var newValue := Node.null;                                                                        
 if ((isAccessible(Stack._state[this], tid) && Stack._lock[this] == tid)) then                      
  moverPath(_B, 1)                                                                                  
 else                                                                                               
  moverPath(_E, 0)                                                                                  
 )                                                                                                  
 )                                                                                                  
}                                                                                                   
                                                                                                    
function {:inline} WriteEval.Stack.head(tid: Tid,this : Stack,newValue: Node,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid) returns (MoverPath) {
 (var isRead := false;                                                                              
 if ((isAccessible(Stack._state[this], tid) && Stack._lock[this] == tid)) then                      
  moverPath(_B, 1)                                                                                  
 else                                                                                               
  moverPath(_E, 0)                                                                                  
 )                                                                                                  
}                                                                                                   
                                                                                                    
/////                                                                                               
                                                                                                    
/////                                                                                               
                                                                                                    
var Stack._lock: [Stack]Tid;                                                                        
                                                                                                    
function {:inline} ReadEval.Stack._lock(tid: Tid,this : Stack,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid) returns (MoverPath) {
 (var isRead := true;                                                                               
 (var newValue := Tid.null;                                                                         
 if (isLocal(Stack._state[this], tid)) then                                                         
  if (isRead) then                                                                                  
   moverPath(_B, 3)                                                                                 
  else                                                                                              
   if (((newValue==tid)||(newValue==Tid.null))) then                                                
    moverPath(_B, 5)                                                                                
   else                                                                                             
    moverPath(_E, 1)                                                                                
 else                                                                                               
  if (isRead) then                                                                                  
   if ((Stack._lock[this]==tid)) then                                                               
    moverPath(_R, 6)                                                                                
   else                                                                                             
    moverPath(_E, 2)                                                                                
  else                                                                                              
   if (((Stack._lock[this]==Tid.null)&&(newValue==tid))) then                                       
    moverPath(_R, 4)                                                                                
   else                                                                                             
    if (((Stack._lock[this]==tid)&&(newValue==Tid.null))) then                                      
     moverPath(_L, 8)                                                                               
    else                                                                                            
     moverPath(_E, 0)                                                                               
 )                                                                                                  
 )                                                                                                  
}                                                                                                   
                                                                                                    
function {:inline} WriteEval.Stack._lock(tid: Tid,this : Stack,newValue: Tid,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid) returns (MoverPath) {
 (var isRead := false;                                                                              
 if (isLocal(Stack._state[this], tid)) then                                                         
  if (isRead) then                                                                                  
   moverPath(_B, 3)                                                                                 
  else                                                                                              
   if (((newValue==tid)||(newValue==Tid.null))) then                                                
    moverPath(_B, 5)                                                                                
   else                                                                                             
    moverPath(_E, 1)                                                                                
 else                                                                                               
  if (isRead) then                                                                                  
   if ((Stack._lock[this]==tid)) then                                                               
    moverPath(_R, 6)                                                                                
   else                                                                                             
    moverPath(_E, 2)                                                                                
  else                                                                                              
   if (((Stack._lock[this]==Tid.null)&&(newValue==tid))) then                                       
    moverPath(_R, 4)                                                                                
   else                                                                                             
    if (((Stack._lock[this]==tid)&&(newValue==Tid.null))) then                                      
     moverPath(_L, 8)                                                                               
    else                                                                                            
     moverPath(_E, 0)                                                                               
 )                                                                                                  
}                                                                                                   
                                                                                                    
/////                                                                                               
                                                                                                    
                                                                                                    
/////                                                                                               
                                                                                                    
/////                                                                                               
                                                                                                    
                                                                                                    
function {:inline} $spec$.Stack.push.IsValidTransition.isSkip(tid:Tid,this : Stack,item : int, Node._state$old: [Node]State,Node.item$old: [Node]int,Node.next$old: [Node]Node,Node._lock$old: [Node]Tid,Stack._state$old: [Stack]State,Stack.head$old: [Stack]Node,Stack._lock$old: [Stack]Tid,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid): bool {
 (forall $this : Node :: true ==> (isShared(Node._state$old[$this]) ==> isShared(Node._state[$this])))
&& (forall $this : Node :: true ==> (isShared(Node._state$old[$this]) ==> Node.item$old[$this] == Node.item[$this]))
&& (forall $this : Node :: true ==> (isShared(Node._state$old[$this]) ==> Node.next$old[$this] == Node.next[$this]))
&& (forall $this : Stack :: true ==> (isShared(Stack._state$old[$this]) ==> isShared(Stack._state[$this])))
&& (forall $this : Stack :: true ==> (isShared(Stack._state$old[$this]) ==> Stack.head$old[$this] == Stack.head[$this]))
}                                                                                                   
                                                                                                    
function {:inline} $spec$.Stack.push.IsValidTransition.0(tid:Tid,this : Stack,item : int, Node._state$old: [Node]State,Node.item$old: [Node]int,Node.next$old: [Node]Node,Node._lock$old: [Node]Tid,Stack._state$old: [Stack]State,Stack.head$old: [Stack]Node,Stack._lock$old: [Stack]Tid,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid): bool {
 ((Node.next[Stack.head[this]]==Stack.head$old[this]))                                              
&& ((Node.item[Stack.head[this]]==item))                                                            
&& (forall $this : Node :: true ==> (isShared(Node._state$old[$this]) ==> isShared(Node._state[$this])))
&& (forall $this : Node :: true ==> (isShared(Node._state$old[$this]) ==> Node.item$old[$this] == Node.item[$this]))
&& (forall $this : Node :: true ==> (isShared(Node._state$old[$this]) ==> Node.next$old[$this] == Node.next[$this]))
&& (forall $this : Stack :: $this != this ==> (isShared(Stack._state$old[$this]) ==> isShared(Stack._state[$this])))
&& (forall $this : Stack :: $this != this ==> (isShared(Stack._state$old[$this]) ==> Stack.head$old[$this] == Stack.head[$this]))
}                                                                                                   
                                                                                                    
procedure Stack.push.specTransition($spec$pc.0$ : bool,$spec$pc.1$ : bool, tid:Tid,this : Stack,item : int, Node._state$old: [Node]State,Node.item$old: [Node]int,Node.next$old: [Node]Node,Node._lock$old: [Node]Tid,Stack._state$old: [Stack]State,Stack.head$old: [Stack]Node,Stack._lock$old: [Stack]Tid,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid) returns ($spec$pc.0$$new : bool, $spec$pc.1$$new : bool);
 ensures (var skips,a0 :=                                                                           
  $spec$.Stack.push.IsValidTransition.isSkip(tid:Tid,this : Stack,item : int, Node._state$old,Node.item$old,Node.next$old,Node._lock$old,Stack._state$old,Stack.head$old,Stack._lock$old,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)
,                                                                                                   
  $spec$.Stack.push.IsValidTransition.0(tid:Tid,this : Stack,item : int, Node._state$old,Node.item$old,Node.next$old,Node._lock$old,Stack._state$old,Stack.head$old,Stack._lock$old,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)
  ;                                                                                                 
 ($spec$pc.0$$new == (($spec$pc.0$ && skips)))                                                      
&& ($spec$pc.1$$new == (($spec$pc.1$ && skips) || ($spec$pc.0$ && a0)))                             
);                                                                                                  
                                                                                                    
                                                                                                    
procedure  Stack.push(tid:Tid, this : Stack, item : int)                                            
modifies Node._state;                                                                               
modifies Node.item;                                                                                 
modifies Node.next;                                                                                 
modifies Node._lock;                                                                                
modifies Stack._state;                                                                              
modifies Stack.head;                                                                                
modifies Stack._lock;                                                                               
                                                                                                    
requires ValidTid(tid);                                                                                    // (15.3): Bad tid
requires isShared(Stack._state[this]);                                                                     // (15.3): this is not global
                                                                                                    
requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
                                                                                                    
ensures StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
{                                                                                                   
 var Node._lock18530_post: [Node]Tid;                                                               
 var $pc18530: Phase;                                                                               
 var $pc18474: Phase;                                                                               
 var Stack.head18530_post: [Stack]Node;                                                             
 var moverPath18509: MoverPath;                                                                     
 var Stack._lock18530: [Stack]Tid;                                                                  
 var tid18530: Tid;                                                                                 
 var $pc18512: Phase;                                                                               
 var moverPath18527: MoverPath;                                                                     
 var this18530_post: Stack;                                                                         
 var Stack.head18512: [Stack]Node;                                                                  
 var Node._lock18527: [Node]Tid;                                                                    
 var $spec$pc.1$18530: bool;                                                                        
 var Stack.head18530: [Stack]Node;                                                                  
 var Node._state18527: [Node]State;                                                                 
 var node18530_post: Node;                                                                          
 var node: Node;                                                                                    
 var Node._lock18530: [Node]Tid;                                                                    
 var Stack._lock18512: [Stack]Tid;                                                                  
 var tmp118509: Node;                                                                               
 var Node.item18474: [Node]int;                                                                     
 var Node.item18530_post: [Node]int;                                                                
 var node18530: Node;                                                                               
 var tmp118527: Node;                                                                               
 var tid18527: Tid;                                                                                 
 var node18527: Node;                                                                               
 var item18512: int;                                                                                
 var item18509: int;                                                                                
 var this18512: Stack;                                                                              
 var $spec$pc.0$18530: bool;                                                                        
 var Node._state18530: [Node]State;                                                                 
 var tid18512: Tid;                                                                                 
 var Node.next18509: [Node]Node;                                                                    
 var node18512: Node;                                                                               
 var this18474: Stack;                                                                              
 var item$118509: int;                                                                              
 var tmp118512: Node;                                                                               
 var item$1: int;                                                                                   
 var $recorded.state18530_post: int;                                                                
 var mover18512: Mover;                                                                             
 var this18509: Stack;                                                                              
 var next$118509: Node;                                                                             
 var Node.item18527: [Node]int;                                                                     
 var path18509: int;                                                                                
 var Node._lock18512: [Node]Tid;                                                                    
 var Node.item18512: [Node]int;                                                                     
 var tmp1: Node;                                                                                    
 var mover18474: Mover;                                                                             
 var tid18474: Tid;                                                                                 
 var Node.item18509: [Node]int;                                                                     
 var $spec$pc.1$18512: bool;                                                                        
 var this$118512: Node;                                                                             
 var item18530_post: int;                                                                           
 var $recorded.state18527: int;                                                                     
 var tid18509: Tid;                                                                                 
 var this18527: Stack;                                                                              
 var Node._state18512: [Node]State;                                                                 
 var Node._lock18474: [Node]Tid;                                                                    
 var Stack._lock18474: [Stack]Tid;                                                                  
 var next$1: Node;                                                                                  
 var item$118512: int;                                                                              
 var tmp118530_post: Node;                                                                          
 var Node.next18530_post: [Node]Node;                                                               
 var Stack._state18530: [Stack]State;                                                               
 var this$1: Node;                                                                                  
 var Node.next18530: [Node]Node;                                                                    
 var moverPath18474: MoverPath;                                                                     
 var item18530: int;                                                                                
 var path18512: int;                                                                                
 var Node.item18530: [Node]int;                                                                     
 var Stack._state18512: [Stack]State;                                                               
 var $pc18509: Phase;                                                                               
 var $recorded.state18474: int;                                                                     
 var Stack._lock18509: [Stack]Tid;                                                                  
 var item18527: int;                                                                                
 var $spec$pc.1$18530_post: bool;                                                                   
 var Node._state18530_post: [Node]State;                                                            
 var $spec$pc.0$18509: bool;                                                                        
 var Stack.head18474: [Stack]Node;                                                                  
 var Stack._state18530_post: [Stack]State;                                                          
 var Stack._lock18527: [Stack]Tid;                                                                  
 var path18474: int;                                                                                
 var $spec$pc.0$18512: bool;                                                                        
 var Stack._state18527: [Stack]State;                                                               
 var Node.next18527: [Node]Node;                                                                    
 var node18474: Node;                                                                               
 var $spec$pc.1$18474: bool;                                                                        
 var next$118512: Node;                                                                             
 var Node.next18512: [Node]Node;                                                                    
 var $spec$pc.0$18527: bool;                                                                        
 var $recorded.state18512: int;                                                                     
 var $spec$pc.1$18527: bool;                                                                        
 var mover18527: Mover;                                                                             
 var item18474: int;                                                                                
 var $recorded.state18530: int;                                                                     
 var this$118509: Node;                                                                             
 var this18530: Stack;                                                                              
 var $recorded.state18509: int;                                                                     
 var Stack._lock18530_post: [Stack]Tid;                                                             
 var path18527: int;                                                                                
 var tmp118530: Node;                                                                               
 var moverPath18512: MoverPath;                                                                     
 var node18509: Node;                                                                               
 var Stack._state18509: [Stack]State;                                                               
 var Stack.head18509: [Stack]Node;                                                                  
 var tmp118474: Node;                                                                               
 var Node._state18474: [Node]State;                                                                 
 var Node.next18474: [Node]Node;                                                                    
 var tid18530_post: Tid;                                                                            
 var $spec$pc.1$18509: bool;                                                                        
 var $pc18527: Phase;                                                                               
 var $spec$pc.0$18530_post: bool;                                                                   
 var Stack.head18527: [Stack]Node;                                                                  
 var mover18509: Mover;                                                                             
 var $spec$pc.0$18474: bool;                                                                        
 var $pc18530_post: Phase;                                                                          
 var Stack._state18474: [Stack]State;                                                               
 var Node._lock18509: [Node]Tid;                                                                    
 var Node._state18509: [Node]State;                                                                 
                                                                                                    
 var $spec$Node._state: [Node]State;                                                                
 var $spec$Node.item: [Node]int;                                                                    
 var $spec$Node.next: [Node]Node;                                                                   
 var $spec$Node._lock: [Node]Tid;                                                                   
 var $spec$Stack._state: [Stack]State;                                                              
 var $spec$Stack.head: [Stack]Node;                                                                 
 var $spec$Stack._lock: [Stack]Tid;                                                                 
 var $spec$pc.0$ : bool; var $spec$pc.1$ : bool;                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 var $pc : Phase;                                                                                   
                                                                                                    
 $spec$Node._state := Node._state;                                                                  
 $spec$Node.item := Node.item;                                                                      
 $spec$Node.next := Node.next;                                                                      
 $spec$Node._lock := Node._lock;                                                                    
 $spec$Stack._state := Stack._state;                                                                
 $spec$Stack.head := Stack.head;                                                                    
 $spec$Stack._lock := Stack._lock;                                                                  
 $spec$pc.0$ := true; $spec$pc.1$ := false;                                                         
                                                                                                    
 $pc := PreCommit;                                                                                  
                                                                                                    
                                                                                                    
 if ($pc == PreCommit) {                                                                            
  assume this != Stack.null;                                                                        
 } else {                                                                                           
  assert this != Stack.null;                                                                               // (19.5): Cannot have potential null deference in left-mover part.
 }                                                                                                  
 assume Stack._lock[this] == Tid.null;                                                              
 $pc := transition($pc, _R);                                                                        
 assert $pc != PhaseError;                                                                                 // (19.5): Reduction failure
 Stack._lock[this] := tid;                                                                          
                                                                                                    
 // 20.5: Node node;                                                                                
                                                                                                    
                                                                                                    
 // 20.5: node = new Node();                                                                        
                                                                                                    
 havoc node;                                                                                        
 assume node != Node.null && isFresh(Node._state[node]);                                            
 assume isFresh($spec$Node._state[node]);                                                           
 Node._state[node] := LOCAL(tid);                                                                   
 assume Node.item[node]  == 0;                                                                      
 assume Node.next[node]  == Node.null;                                                              
 assume Node._lock[node]  == Tid.null;                                                              
                                                                                                    
 // 20.5: Node tmp1;                                                                                
                                                                                                    
                                                                                                    
 // 20.5: tmp1 := this.head;                                                                        
                                                                                                    
                                                                                                    
 moverPath18474 := ReadEval.Stack.head(tid: Tid,this: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 mover18474 := m#moverPath(moverPath18474);                                                         
 path18474 := p#moverPath(moverPath18474);                                                          
 assume Node._state18474 == Node._state && Node.item18474 == Node.item && Node.next18474 == Node.next && Node._lock18474 == Node._lock && Stack._state18474 == Stack._state && Stack.head18474 == Stack.head && Stack._lock18474 == Stack._lock && tmp118474 == tmp1 && node18474 == node && item18474 == item && this18474 == this && tid18474 == tid && $pc18474 == $pc && $spec$pc.0$18474 == $spec$pc.0$ && $spec$pc.1$18474 == $spec$pc.1$;
 assume $recorded.state18474 == 1;                                                                  
 if ($pc == PreCommit) {                                                                            
  assume this != Stack.null;                                                                        
 } else {                                                                                           
  assert this != Stack.null;                                                                               // (20.5): Cannot have potential null deference in left-mover part.
 }                                                                                                  
                                                                                                    
 $pc := transition($pc, mover18474);                                                                
 assert $pc != PhaseError;                                                                                 // (20.5): Reduction failure
 tmp1 := Stack.head[this];                                                                          
 // inlined: node.init(item,tmp1)}                                                                  
 exit$1_top:                                                                                        
                                                                                                    
 // 20.5: int item$1;                                                                               
                                                                                                    
                                                                                                    
 // 20.5: Node next$1;                                                                              
                                                                                                    
                                                                                                    
 // 20.5: Node this$1;                                                                              
                                                                                                    
                                                                                                    
 // 20.5: item$1 = item;                                                                            
                                                                                                    
 item$1 := item;                                                                                    
                                                                                                    
 // 20.5: next$1 = tmp1;                                                                            
                                                                                                    
 next$1 := tmp1;                                                                                    
                                                                                                    
 // 20.5: this$1 = node;                                                                            
                                                                                                    
 this$1 := node;                                                                                    
                                                                                                    
 // 5.3: assume this$1.item == 0;                                                                   
                                                                                                    
 assume (Node.item[this$1]==0);                                                                     
                                                                                                    
 // 5.3: assume this$1.next == Node.null;                                                           
                                                                                                    
 assume (Node.next[this$1]==Node.null);                                                             
                                                                                                    
                                                                                                    
 // 6.5: this$1.item := item$1;                                                                     
                                                                                                    
                                                                                                    
 moverPath18509 := WriteEval.Node.item(tid: Tid,this$1: Node,item$1: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 mover18509 := m#moverPath(moverPath18509);                                                         
 path18509 := p#moverPath(moverPath18509);                                                          
 assume Node._state18509 == Node._state && Node.item18509 == Node.item && Node.next18509 == Node.next && Node._lock18509 == Node._lock && Stack._state18509 == Stack._state && Stack.head18509 == Stack.head && Stack._lock18509 == Stack._lock && this$118509 == this$1 && next$118509 == next$1 && item$118509 == item$1 && tmp118509 == tmp1 && node18509 == node && item18509 == item && this18509 == this && tid18509 == tid && $pc18509 == $pc && $spec$pc.0$18509 == $spec$pc.0$ && $spec$pc.1$18509 == $spec$pc.1$;
 assume $recorded.state18509 == 1;                                                                  
 if ($pc == PreCommit) {                                                                            
  assume this$1 != Node.null;                                                                       
 } else {                                                                                           
  assert this$1 != Node.null;                                                                              // (6.5): Cannot have potential null deference in left-mover part.
 }                                                                                                  
 $pc := transition($pc, mover18509);                                                                
 assert $pc != PhaseError;                                                                                 // (6.5): Reduction failure
 Node.item[this$1] := item$1;                                                                       
                                                                                                    
                                                                                                    
 // 7.5: this$1.next := next$1;                                                                     
                                                                                                    
                                                                                                    
 moverPath18512 := WriteEval.Node.next(tid: Tid,this$1: Node,next$1: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 mover18512 := m#moverPath(moverPath18512);                                                         
 path18512 := p#moverPath(moverPath18512);                                                          
 assume Node._state18512 == Node._state && Node.item18512 == Node.item && Node.next18512 == Node.next && Node._lock18512 == Node._lock && Stack._state18512 == Stack._state && Stack.head18512 == Stack.head && Stack._lock18512 == Stack._lock && this$118512 == this$1 && next$118512 == next$1 && item$118512 == item$1 && tmp118512 == tmp1 && node18512 == node && item18512 == item && this18512 == this && tid18512 == tid && $pc18512 == $pc && $spec$pc.0$18512 == $spec$pc.0$ && $spec$pc.1$18512 == $spec$pc.1$;
 assume $recorded.state18512 == 1;                                                                  
 if ($pc == PreCommit) {                                                                            
  assume this$1 != Node.null;                                                                       
 } else {                                                                                           
  assert this$1 != Node.null;                                                                              // (7.5): Cannot have potential null deference in left-mover part.
 }                                                                                                  
 $pc := transition($pc, mover18512);                                                                
 assert $pc != PhaseError;                                                                                 // (7.5): Reduction failure
 Node.next[this$1] := next$1;                                                                       
 if (isLocal(Node._state[next$1], tid)) {                                                           
  Node._state[next$1] := SHARED();                                                                  
  assert isSharedAssignable(Node._state[Node.next[next$1]]);                                               // (7.5): next$1 became shared, but next$1.next may not be shared.
 }                                                                                                  
                                                                                                    
                                                                                                    
 // 5.29: break exit$1;                                                                             
                                                                                                    
 goto exit$1_bottom;                                                                                
 exit$1_bottom:                                                                                     
                                                                                                    
                                                                                                    
 // 21.5: this.head := node;                                                                        
                                                                                                    
                                                                                                    
 moverPath18527 := WriteEval.Stack.head(tid: Tid,this: Stack,node: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 mover18527 := m#moverPath(moverPath18527);                                                         
 path18527 := p#moverPath(moverPath18527);                                                          
 assume Node._state18527 == Node._state && Node.item18527 == Node.item && Node.next18527 == Node.next && Node._lock18527 == Node._lock && Stack._state18527 == Stack._state && Stack.head18527 == Stack.head && Stack._lock18527 == Stack._lock && tmp118527 == tmp1 && node18527 == node && item18527 == item && this18527 == this && tid18527 == tid && $pc18527 == $pc && $spec$pc.0$18527 == $spec$pc.0$ && $spec$pc.1$18527 == $spec$pc.1$;
 assume $recorded.state18527 == 1;                                                                  
 if ($pc == PreCommit) {                                                                            
  assume this != Stack.null;                                                                        
 } else {                                                                                           
  assert this != Stack.null;                                                                               // (21.5): Cannot have potential null deference in left-mover part.
 }                                                                                                  
 $pc := transition($pc, mover18527);                                                                
 assert $pc != PhaseError;                                                                                 // (21.5): Reduction failure
 Stack.head[this] := node;                                                                          
 if (isLocal(Node._state[node], tid)) {                                                             
  Node._state[node] := SHARED();                                                                    
  assert isSharedAssignable(Node._state[Node.next[node]]);                                                 // (21.5): node became shared, but node.next may not be shared.
 }                                                                                                  
                                                                                                    
 if ($pc == PreCommit) {                                                                            
  assume this != Stack.null;                                                                        
 } else {                                                                                           
  assert this != Stack.null;                                                                               // (22.5): Cannot have potential null deference in left-mover part.
 }                                                                                                  
 assert Stack._lock[this] == tid;                                                                          // (22.5): lock not held
 $pc := transition($pc, _L);                                                                        
 assert $pc != PhaseError;                                                                                 // (22.5): Reduction failure
 Stack._lock[this] := Tid.null;                                                                     
                                                                                                    
 // 18.30: // return;                                                                               
                                                                                                    
 assume Node._state18530 == Node._state && Node.item18530 == Node.item && Node.next18530 == Node.next && Node._lock18530 == Node._lock && Stack._state18530 == Stack._state && Stack.head18530 == Stack.head && Stack._lock18530 == Stack._lock && tmp118530 == tmp1 && node18530 == node && item18530 == item && this18530 == this && tid18530 == tid && $spec$pc.0$18530 == $spec$pc.0$ && $spec$pc.1$18530 == $spec$pc.1$;
 assume $recorded.state18530 == 1;                                                                  
                                                                                                    
 call $spec$pc.0$, $spec$pc.1$ :=                                                                   
 Stack.push.specTransition($spec$pc.0$, $spec$pc.1$, tid,this,item, $spec$Node._state,$spec$Node.item,$spec$Node.next,$spec$Node._lock,$spec$Stack._state,$spec$Stack.head,$spec$Stack._lock,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 assume Node._state18530_post == Node._state && Node.item18530_post == Node.item && Node.next18530_post == Node.next && Node._lock18530_post == Node._lock && Stack._state18530_post == Stack._state && Stack.head18530_post == Stack.head && Stack._lock18530_post == Stack._lock && tmp118530_post == tmp1 && node18530_post == node && item18530_post == item && this18530_post == this && tid18530_post == tid && $spec$pc.0$18530_post == $spec$pc.0$ && $spec$pc.1$18530_post == $spec$pc.1$;
 assume $recorded.state18530_post == 1;                                                             
 assert $spec$pc.1$;                                                                                       // (18.30): Method returns before completing actions in spec
 return;                                                                                            
}                                                                                                   
                                                                                                    
                                                                                                    
function {:inline} $spec$.Stack.pop.IsValidTransition.isSkip(tid:Tid,this : Stack,$result : int,$result$old : int, Node._state$old: [Node]State,Node.item$old: [Node]int,Node.next$old: [Node]Node,Node._lock$old: [Node]Tid,Stack._state$old: [Stack]State,Stack.head$old: [Stack]Node,Stack._lock$old: [Stack]Tid,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid): bool {
 (forall $this : Node :: true ==> (isShared(Node._state$old[$this]) ==> isShared(Node._state[$this])))
&& (forall $this : Node :: true ==> (isShared(Node._state$old[$this]) ==> Node.item$old[$this] == Node.item[$this]))
&& (forall $this : Node :: true ==> (isShared(Node._state$old[$this]) ==> Node.next$old[$this] == Node.next[$this]))
&& (forall $this : Stack :: true ==> (isShared(Stack._state$old[$this]) ==> isShared(Stack._state[$this])))
&& (forall $this : Stack :: true ==> (isShared(Stack._state$old[$this]) ==> Stack.head$old[$this] == Stack.head[$this]))
}                                                                                                   
                                                                                                    
function {:inline} $spec$.Stack.pop.IsValidTransition.0(tid:Tid,this : Stack,$result : int,$result$old : int, Node._state$old: [Node]State,Node.item$old: [Node]int,Node.next$old: [Node]Node,Node._lock$old: [Node]Tid,Stack._state$old: [Stack]State,Stack.head$old: [Stack]Node,Stack._lock$old: [Stack]Tid,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid): bool {
 ((Stack.head$old[this]!=Node.null))                                                                
&& (($result==Node.item$old[Stack.head$old[this]]))                                                 
&& ((Stack.head[this]==Node.next$old[Stack.head$old[this]]))                                        
&& (forall $this : Node :: true ==> (isShared(Node._state$old[$this]) ==> isShared(Node._state[$this])))
&& (forall $this : Node :: true ==> (isShared(Node._state$old[$this]) ==> Node.item$old[$this] == Node.item[$this]))
&& (forall $this : Node :: true ==> (isShared(Node._state$old[$this]) ==> Node.next$old[$this] == Node.next[$this]))
&& (forall $this : Stack :: $this != this ==> (isShared(Stack._state$old[$this]) ==> isShared(Stack._state[$this])))
&& (forall $this : Stack :: $this != this ==> (isShared(Stack._state$old[$this]) ==> Stack.head$old[$this] == Stack.head[$this]))
}                                                                                                   
                                                                                                    
procedure Stack.pop.specTransition($spec$pc.0$ : bool,$spec$pc.1$ : bool, tid:Tid,this : Stack,$result : int,$result$old : int, Node._state$old: [Node]State,Node.item$old: [Node]int,Node.next$old: [Node]Node,Node._lock$old: [Node]Tid,Stack._state$old: [Stack]State,Stack.head$old: [Stack]Node,Stack._lock$old: [Stack]Tid,Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid) returns ($spec$pc.0$$new : bool, $spec$pc.1$$new : bool);
 ensures (var skips,a0 :=                                                                           
  $spec$.Stack.pop.IsValidTransition.isSkip(tid:Tid,this : Stack,$result : int,$result$old : int, Node._state$old,Node.item$old,Node.next$old,Node._lock$old,Stack._state$old,Stack.head$old,Stack._lock$old,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)
,                                                                                                   
  $spec$.Stack.pop.IsValidTransition.0(tid:Tid,this : Stack,$result : int,$result$old : int, Node._state$old,Node.item$old,Node.next$old,Node._lock$old,Stack._state$old,Stack.head$old,Stack._lock$old,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)
  ;                                                                                                 
 ($spec$pc.0$$new == (($spec$pc.0$ && skips)))                                                      
&& ($spec$pc.1$$new == (($spec$pc.1$ && skips) || ($spec$pc.0$ && a0)))                             
);                                                                                                  
                                                                                                    
                                                                                                    
procedure  Stack.pop(tid:Tid, this : Stack)                                                         
returns ($result : int)                                                                             
modifies Node._state;                                                                               
modifies Node.item;                                                                                 
modifies Node.next;                                                                                 
modifies Node._lock;                                                                                
modifies Stack._state;                                                                              
modifies Stack.head;                                                                                
modifies Stack._lock;                                                                               
                                                                                                    
requires ValidTid(tid);                                                                                    // (25.3): Bad tid
requires isShared(Stack._state[this]);                                                                     // (25.3): this is not global
                                                                                                    
requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
                                                                                                    
ensures StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
{                                                                                                   
 var tmp3: Node;                                                                                    
 var $recorded.state18564_bottom: int;                                                              
 var Stack.head18573: [Stack]Node;                                                                  
 var Stack._state18595_post: [Stack]State;                                                          
 var Stack._state18544: [Stack]State;                                                               
 var Node._lock18591: [Node]Tid;                                                                    
 var Stack._state18573: [Stack]State;                                                               
 var Stack._lock18588: [Stack]Tid;                                                                  
 var Stack.head18595_post: [Stack]Node;                                                             
 var Node._state18544: [Node]State;                                                                 
 var $pc18585: Phase;                                                                               
 var Stack._state18576: [Stack]State;                                                               
 var Node._state18585: [Node]State;                                                                 
 var $spec$$result18573: int;                                                                       
 var tmp418595: Node;                                                                               
 var Stack._lock18599_post: [Stack]Tid;                                                             
 var Stack.head18559: [Stack]Node;                                                                  
 var this18544: Stack;                                                                              
 var tmp418585: Node;                                                                               
 var Node._lock18585: [Node]Tid;                                                                    
 var Node._state18559_post: [Node]State;                                                            
 var Node.next18585: [Node]Node;                                                                    
 var moverPath18573: MoverPath;                                                                     
 var tid18595: Tid;                                                                                 
 var $result18576: int;                                                                             
 var Node._lock18595_post: [Node]Tid;                                                               
 var value18599_post: int;                                                                          
 var tmp4: Node;                                                                                    
 var $spec$pc.1$18559: bool;                                                                        
 var Stack._lock18591: [Stack]Tid;                                                                  
 var $pc18595: Phase;                                                                               
 var value18595: int;                                                                               
 var $spec$pc.1$18599: bool;                                                                        
 var this18599: Stack;                                                                              
 var $recorded.state18595_post: int;                                                                
 var $spec$$result18576: int;                                                                       
 var Stack._lock18559_post: [Stack]Tid;                                                             
 var Stack._state18585: [Stack]State;                                                               
 var Stack._lock18585: [Stack]Tid;                                                                  
 var $recorded.state18576: int;                                                                     
 var Stack.head18599_post: [Stack]Node;                                                             
 var Stack.head18591: [Stack]Node;                                                                  
 var tmp618591: Node;                                                                               
 var Stack._lock18559: [Stack]Tid;                                                                  
 var Node.item18595_post: [Node]int;                                                                
 var Node._lock18576: [Node]Tid;                                                                    
 var $pc18559_post: Phase;                                                                          
 var Node.next18599: [Node]Node;                                                                    
 var this18564_bottom: Stack;                                                                       
 var tmp418595_post: Node;                                                                          
 var tmp418588: Node;                                                                               
 var $pc18559: Phase;                                                                               
 var $result18599: int;                                                                             
 var tmp518599: Node;                                                                               
 var tid18564_bottom: Tid;                                                                          
 var $result18588: int;                                                                             
 var path18576: int;                                                                                
 var tmp518599_post: Node;                                                                          
 var this18573: Stack;                                                                              
 var $result18599_post: int;                                                                        
 var Stack._state18559: [Stack]State;                                                               
 var Stack._state18591: [Stack]State;                                                               
 var tmp218559_post: bool;                                                                          
 var Node.next18588: [Node]Node;                                                                    
 var tmp318559: Node;                                                                               
 var Stack.head18585: [Stack]Node;                                                                  
 var Node.next18573: [Node]Node;                                                                    
 var Node.next18591: [Node]Node;                                                                    
 var $spec$$result18595: int;                                                                       
 var this18595: Stack;                                                                              
 var tmp2: bool;                                                                                    
 var tmp618599_post: Node;                                                                          
 var Stack._lock18576: [Stack]Tid;                                                                  
 var Node._state18576: [Node]State;                                                                 
 var Stack._state18559_post: [Stack]State;                                                          
 var $result18564: int;                                                                             
 var Node._lock18559: [Node]Tid;                                                                    
 var Node._state18588: [Node]State;                                                                 
 var Node.item18544: [Node]int;                                                                     
 var value18573: int;                                                                               
 var Stack._lock18544: [Stack]Tid;                                                                  
 var tmp518595: Node;                                                                               
 var tid18588: Tid;                                                                                 
 var $spec$pc.0$18585: bool;                                                                        
 var tid18564: Tid;                                                                                 
 var Node._lock18559_post: [Node]Tid;                                                               
 var tmp518585: Node;                                                                               
 var Node.item18564: [Node]int;                                                                     
 var tmp518595_post: Node;                                                                          
 var $pc18564: Phase;                                                                               
 var $spec$pc.1$18544: bool;                                                                        
 var $spec$pc.1$18559_post: bool;                                                                   
 var value: int;                                                                                    
 var $spec$pc.1$$loopHead18564: bool;                                                               
 var Node.next18544: [Node]Node;                                                                    
 var tmp518588: Node;                                                                               
 var $pc18576: Phase;                                                                               
 var Node._lock18599_post: [Node]Tid;                                                               
 var $spec$pc.0$18591: bool;                                                                        
 var Node.next18559: [Node]Node;                                                                    
 var moverPath18591: MoverPath;                                                                     
 var tid18544: Tid;                                                                                 
 var Stack._lock18595: [Stack]Tid;                                                                  
 var path18591: int;                                                                                
 var Node._state18599: [Node]State;                                                                 
 var value18585: int;                                                                               
 var tmp218559: bool;                                                                               
 var Stack._state18595: [Stack]State;                                                               
 var $recorded.state18591: int;                                                                     
 var $spec$pc.1$18585: bool;                                                                        
 var $pc18544: Phase;                                                                               
 var Stack._state18564: [Stack]State;                                                               
 var Stack.head18564: [Stack]Node;                                                                  
 var $result18595_post: int;                                                                        
 var $spec$pc.0$18559_post: bool;                                                                   
 var Node.item18559_post: [Node]int;                                                                
 var tid18591: Tid;                                                                                 
 var path18585: int;                                                                                
 var Node.item18588: [Node]int;                                                                     
 var Node._state18559: [Node]State;                                                                 
 var value18576: int;                                                                               
 var $spec$pc.1$18576: bool;                                                                        
 var Stack._state18599: [Stack]State;                                                               
 var Node.next18564: [Node]Node;                                                                    
 var $pc18573: Phase;                                                                               
 var $spec$pc.1$18595_post: bool;                                                                   
 var $spec$pc.0$18564_bottom: bool;                                                                 
 var tmp418573: Node;                                                                               
 var tmp418591: Node;                                                                               
 var Node._state18591: [Node]State;                                                                 
 var $spec$pc.1$18588: bool;                                                                        
 var $spec$pc.0$18595_post: bool;                                                                   
 var mover18573: Mover;                                                                             
 var moverPath18544: MoverPath;                                                                     
 var Node._lock18588: [Node]Tid;                                                                    
 var value18595_post: int;                                                                          
 var Node.item18573: [Node]int;                                                                     
 var $spec$pc.1$18591: bool;                                                                        
 var tid18595_post: Tid;                                                                            
 var $spec$pc.0$18599: bool;                                                                        
 var tmp418599_post: Node;                                                                          
 var $spec$$result18599_post: int;                                                                  
 var moverPath18576: MoverPath;                                                                     
 var Node._state18595: [Node]State;                                                                 
 var $spec$$result18595_post: int;                                                                  
 var $result18544: int;                                                                             
 var $recorded.state18595: int;                                                                     
 var moverPath18588: MoverPath;                                                                     
 var Node._lock18599: [Node]Tid;                                                                    
 var Stack.head18544: [Stack]Node;                                                                  
 var this18559_post: Stack;                                                                         
 var Node._lock18564_bottom: [Node]Tid;                                                             
 var $spec$$result18585: int;                                                                       
 var Node.item18585: [Node]int;                                                                     
 var tmp618599: Node;                                                                               
 var $pc18588: Phase;                                                                               
 var $pc18595_post: Phase;                                                                          
 var $result18564_bottom: int;                                                                      
 var Node.item18564_bottom: [Node]int;                                                              
 var Stack._lock18564: [Stack]Tid;                                                                  
 var $result18559: int;                                                                             
 var mover18585: Mover;                                                                             
 var this18564: Stack;                                                                              
 var tmp618595_post: Node;                                                                          
 var tid18573: Tid;                                                                                 
 var $result18559_post: int;                                                                        
 var Stack._lock18595_post: [Stack]Tid;                                                             
 var $spec$pc.0$18544: bool;                                                                        
 var tmp618595: Node;                                                                               
 var mover18576: Mover;                                                                             
 var Node.item18559: [Node]int;                                                                     
 var Node.item18576: [Node]int;                                                                     
 var tmp5: Node;                                                                                    
 var mover18544: Mover;                                                                             
 var tmp6: Node;                                                                                    
 var $spec$pc.0$18599_post: bool;                                                                   
 var $recorded.state18588: int;                                                                     
 var tmp418576: Node;                                                                               
 var $recorded.state18585: int;                                                                     
 var $spec$$result18544: int;                                                                       
 var tid18585: Tid;                                                                                 
 var $spec$pc.0$18588: bool;                                                                        
 var Stack.head18588: [Stack]Node;                                                                  
 var Node._state18573: [Node]State;                                                                 
 var tid18559_post: Tid;                                                                            
 var $recorded.state18599_post: int;                                                                
 var Node.next18595: [Node]Node;                                                                    
 var Node._state18564_bottom: [Node]State;                                                          
 var $spec$pc.1$18599_post: bool;                                                                   
 var $pc18599_post: Phase;                                                                          
 var tmp318544: Node;                                                                               
 var $result18585: int;                                                                             
 var Stack.head18599: [Stack]Node;                                                                  
 var path18573: int;                                                                                
 var $spec$$result18588: int;                                                                       
 var tmp618588: Node;                                                                               
 var $spec$$result18564_bottom: int;                                                                
 var Node.next18595_post: [Node]Node;                                                               
 var $spec$pc.0$$loopHead18564: bool;                                                               
 var $spec$$result18559_post: int;                                                                  
 var $spec$pc.0$18573: bool;                                                                        
 var Node.item18599: [Node]int;                                                                     
 var path18544: int;                                                                                
 var tid18599: Tid;                                                                                 
 var Node._state18564: [Node]State;                                                                 
 var $spec$pc.0$18595: bool;                                                                        
 var Stack.head18595: [Stack]Node;                                                                  
 var Node._lock18544: [Node]Tid;                                                                    
 var this18595_post: Stack;                                                                         
 var path18588: int;                                                                                
 var value18599: int;                                                                               
 var $spec$pc.1$18595: bool;                                                                        
 var $spec$pc.0$18576: bool;                                                                        
 var Stack.head18559_post: [Stack]Node;                                                             
 var this18576: Stack;                                                                              
 var $spec$pc.0$18559: bool;                                                                        
 var $spec$$result18599: int;                                                                       
 var value18588: int;                                                                               
 var this18559: Stack;                                                                              
 var $spec$$result18564: int;                                                                       
 var $result18573: int;                                                                             
 var tid18599_post: Tid;                                                                            
 var Node.item18599_post: [Node]int;                                                                
 var $recorded.state18564: int;                                                                     
 var tid18576: Tid;                                                                                 
 var Node.item18595: [Node]int;                                                                     
 var tid18559: Tid;                                                                                 
 var mover18588: Mover;                                                                             
 var Stack.head18564_bottom: [Stack]Node;                                                           
 var $result18591: int;                                                                             
 var $recorded.state18559_post: int;                                                                
 var moverPath18585: MoverPath;                                                                     
 var $spec$pc.1$18564_bottom: bool;                                                                 
 var Node.item18591: [Node]int;                                                                     
 var Node._lock18595: [Node]Tid;                                                                    
 var Node._lock18564: [Node]Tid;                                                                    
 var $spec$pc.0$18564: bool;                                                                        
 var tmp418599: Node;                                                                               
 var Stack._state18564_bottom: [Stack]State;                                                        
 var Node.next18559_post: [Node]Node;                                                               
 var $recorded.state18544: int;                                                                     
 var this18599_post: Stack;                                                                         
 var Node._lock18573: [Node]Tid;                                                                    
 var tmp218544: bool;                                                                               
 var tmp618585: Node;                                                                               
 var Node._state18599_post: [Node]State;                                                            
 var $spec$pc.1$18573: bool;                                                                        
 var $recorded.state18599: int;                                                                     
 var Stack._lock18573: [Stack]Tid;                                                                  
 var Node._state18595_post: [Node]State;                                                            
 var Stack.head18576: [Stack]Node;                                                                  
 var $pc18591: Phase;                                                                               
 var $spec$$result18559: int;                                                                       
 var $recorded.state18559: int;                                                                     
 var $spec$$result18591: int;                                                                       
 var $recorded.state18573: int;                                                                     
 var Stack._state18588: [Stack]State;                                                               
 var tmp318559_post: Node;                                                                          
 var $pc18599: Phase;                                                                               
 var this18585: Stack;                                                                              
 var Node.next18564_bottom: [Node]Node;                                                             
 var this18588: Stack;                                                                              
 var tmp518591: Node;                                                                               
 var $result18595: int;                                                                             
 var Stack._lock18564_bottom: [Stack]Tid;                                                           
 var this18591: Stack;                                                                              
 var phase18564: Phase;                                                                             
 var $pc18564_bottom: Phase;                                                                        
 var Stack._lock18599: [Stack]Tid;                                                                  
 var Node.next18576: [Node]Node;                                                                    
 var Node.next18599_post: [Node]Node;                                                               
 var mover18591: Mover;                                                                             
 var value18591: int;                                                                               
 var $spec$pc.1$18564: bool;                                                                        
 var Stack._state18599_post: [Stack]State;                                                          
                                                                                                    
 var $spec$Node._state: [Node]State;                                                                
 var $spec$Node.item: [Node]int;                                                                    
 var $spec$Node.next: [Node]Node;                                                                   
 var $spec$Node._lock: [Node]Tid;                                                                   
 var $spec$Stack._state: [Stack]State;                                                              
 var $spec$Stack.head: [Stack]Node;                                                                 
 var $spec$Stack._lock: [Stack]Tid;                                                                 
 var $spec$pc.0$ : bool; var $spec$pc.1$ : bool;                                                    
 var $spec$$result : int;                                                                           
                                                                                                    
                                                                                                    
 var $pc : Phase;                                                                                   
                                                                                                    
 $spec$Node._state := Node._state;                                                                  
 $spec$Node.item := Node.item;                                                                      
 $spec$Node.next := Node.next;                                                                      
 $spec$Node._lock := Node._lock;                                                                    
 $spec$Stack._state := Stack._state;                                                                
 $spec$Stack.head := Stack.head;                                                                    
 $spec$Stack._lock := Stack._lock;                                                                  
 $spec$pc.0$ := true; $spec$pc.1$ := false;                                                         
                                                                                                    
 $pc := PreCommit;                                                                                  
                                                                                                    
                                                                                                    
 if ($pc == PreCommit) {                                                                            
  assume this != Stack.null;                                                                        
 } else {                                                                                           
  assert this != Stack.null;                                                                               // (30.5): Cannot have potential null deference in left-mover part.
 }                                                                                                  
 assume Stack._lock[this] == Tid.null;                                                              
 $pc := transition($pc, _R);                                                                        
 assert $pc != PhaseError;                                                                                 // (30.5): Reduction failure
 Stack._lock[this] := tid;                                                                          
 assume Node._state18564 == Node._state && Node.item18564 == Node.item && Node.next18564 == Node.next && Node._lock18564 == Node._lock && Stack._state18564 == Stack._state && Stack.head18564 == Stack.head && Stack._lock18564 == Stack._lock && $result18564 == $result && this18564 == this && tid18564 == tid && $spec$pc.0$18564 == $spec$pc.0$ && $spec$pc.1$18564 == $spec$pc.1$ && $spec$$result18564 == $spec$$result;
 assume $recorded.state18564 == 1;                                                                  
                                                                                                    
 // 31.5: while (true)                                                                              
                                                                                                    
 phase18564 := $pc;                                                                                 
 $spec$Node._state := Node._state;                                                                  
 $spec$Node.item := Node.item;                                                                      
 $spec$Node.next := Node.next;                                                                      
 $spec$Node._lock := Node._lock;                                                                    
 $spec$Stack._state := Stack._state;                                                                
 $spec$Stack.head := Stack.head;                                                                    
 $spec$Stack._lock := Stack._lock;                                                                  
 $spec$$result := $result;                                                                          
 $spec$pc.0$$loopHead18564 := $spec$pc.0$;                                                          
 $spec$pc.1$$loopHead18564 := $spec$pc.1$;                                                          
 assert $spec$pc.0$ || $spec$pc.1$;                                                                        // (31.5): Cannot construct possible Spec States for loop head.
 while (true)                                                                                       
                                                                                                    
  invariant ValidTid(tid);                                                                                 // (25.3): Bad tid
  invariant isShared(Stack._state[this]);                                                                  // (25.3): this is not global
                                                                                                    
  invariant StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
  invariant (isAccessible(Stack._state[this], tid) && Stack._lock[this] == tid);                    
  invariant (forall _this : Node :: Invariant.Y_Node.item(tid : Tid, _this, Node.item[_this] ,Node._state18564,Node.item18564,Node.next18564,Node._lock18564,Stack._state18564,Stack.head18564,Stack._lock18564));       // (31.5): Loop does not preserve yields_as annotation for field item
  invariant (forall _this : Node :: Invariant.Y_Node.next(tid : Tid, _this, Node.next[_this] ,Node._state18564,Node.item18564,Node.next18564,Node._lock18564,Stack._state18564,Stack.head18564,Stack._lock18564));       // (31.5): Loop does not preserve yields_as annotation for field next
  invariant (forall _this : Stack :: Invariant.Y_Stack.head(tid : Tid, _this, Stack.head[_this] ,Node._state18564,Node.item18564,Node.next18564,Node._lock18564,Stack._state18564,Stack.head18564,Stack._lock18564));       // (31.5): Loop does not preserve yields_as annotation for field head
  invariant phase18564 == $pc;                                                                             // (31.5): Phase must be invariant at loop head
  invariant $pc == PreCommit;                                                                              // (31.5): Potentially infinite loop cannot be in post-commit phase.
  invariant $spec$Node._state == Node._state;                                                       
  invariant $spec$Node.item == Node.item;                                                           
  invariant $spec$Node.next == Node.next;                                                           
  invariant $spec$Node._lock == Node._lock;                                                         
  invariant $spec$Stack._state == Stack._state;                                                     
  invariant $spec$Stack.head == Stack.head;                                                         
  invariant $spec$Stack._lock == Stack._lock;                                                       
  invariant $spec$$result == $result;                                                               
  invariant $spec$pc.0$;                                                                            
 {                                                                                                  
                                                                                                    
  // 31.22: boolean tmp2;                                                                           
                                                                                                    
                                                                                                    
  // 31.12: Node tmp3;                                                                              
                                                                                                    
                                                                                                    
  // 31.12: tmp3 := this.head;                                                                      
                                                                                                    
                                                                                                    
  moverPath18544 := ReadEval.Stack.head(tid: Tid,this: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
  mover18544 := m#moverPath(moverPath18544);                                                        
  path18544 := p#moverPath(moverPath18544);                                                         
  assume Node._state18544 == Node._state && Node.item18544 == Node.item && Node.next18544 == Node.next && Node._lock18544 == Node._lock && Stack._state18544 == Stack._state && Stack.head18544 == Stack.head && Stack._lock18544 == Stack._lock && tmp318544 == tmp3 && tmp218544 == tmp2 && $result18544 == $result && this18544 == this && tid18544 == tid && $pc18544 == $pc && $spec$pc.0$18544 == $spec$pc.0$ && $spec$pc.1$18544 == $spec$pc.1$ && $spec$$result18544 == $spec$$result;
  assume $recorded.state18544 == 1;                                                                 
  if ($pc == PreCommit) {                                                                           
   assume this != Stack.null;                                                                       
  } else {                                                                                          
   assert this != Stack.null;                                                                              // (31.12): Cannot have potential null deference in left-mover part.
  }                                                                                                 
                                                                                                    
  $pc := transition($pc, mover18544);                                                               
  assert $pc != PhaseError;                                                                                // (31.12): Reduction failure
  tmp3 := Stack.head[this];                                                                         
                                                                                                    
  // 31.22: tmp2 = tmp3 == Node.null;                                                               
                                                                                                    
  tmp2 := (tmp3==Node.null);                                                                        
  if (!(tmp2)) {                                                                                    
                                                                                                    
   // 31.5: break;                                                                                  
                                                                                                    
   break;                                                                                           
  } else {                                                                                          
  }                                                                                                 
  if ($pc == PreCommit) {                                                                           
   assume this != Stack.null;                                                                       
  } else {                                                                                          
   assert this != Stack.null;                                                                              // (34.7): Cannot have potential null deference in left-mover part.
  }                                                                                                 
  assert Stack._lock[this] == tid;                                                                         // (34.7): lock not held
  $pc := transition($pc, _L);                                                                       
  assert $pc != PhaseError;                                                                                // (34.7): Reduction failure
  Stack._lock[this] := Tid.null;                                                                    
                                                                                                    
  // 35.7: yield;                                                                                   
                                                                                                    
  assume Node._state18559 == Node._state && Node.item18559 == Node.item && Node.next18559 == Node.next && Node._lock18559 == Node._lock && Stack._state18559 == Stack._state && Stack.head18559 == Stack.head && Stack._lock18559 == Stack._lock && tmp318559 == tmp3 && tmp218559 == tmp2 && $result18559 == $result && this18559 == this && tid18559 == tid && $spec$pc.0$18559 == $spec$pc.0$ && $spec$pc.1$18559 == $spec$pc.1$ && $spec$$result18559 == $spec$$result;
  assume $recorded.state18559 == 1;                                                                 
                                                                                                    
  call $spec$pc.0$, $spec$pc.1$ :=                                                                  
  Stack.pop.specTransition($spec$pc.0$, $spec$pc.1$, tid,this,$result : int,$spec$$result : int, $spec$Node._state,$spec$Node.item,$spec$Node.next,$spec$Node._lock,$spec$Stack._state,$spec$Stack.head,$spec$Stack._lock,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
  call Yield(tid);                                                                                  
  $spec$Node._state := Node._state;$spec$Node.item := Node.item;$spec$Node.next := Node.next;$spec$Node._lock := Node._lock;$spec$Stack._state := Stack._state;$spec$Stack.head := Stack.head;$spec$Stack._lock := Stack._lock;
  $spec$$result := $result;                                                                         
  $pc := PreCommit;                                                                                 
  assume Node._state18559_post == Node._state && Node.item18559_post == Node.item && Node.next18559_post == Node.next && Node._lock18559_post == Node._lock && Stack._state18559_post == Stack._state && Stack.head18559_post == Stack.head && Stack._lock18559_post == Stack._lock && tmp318559_post == tmp3 && tmp218559_post == tmp2 && $result18559_post == $result && this18559_post == this && tid18559_post == tid && $spec$pc.0$18559_post == $spec$pc.0$ && $spec$pc.1$18559_post == $spec$pc.1$ && $spec$$result18559_post == $spec$$result;
  assume $recorded.state18559_post == 1;                                                            
  assert $spec$pc.0$ || $spec$pc.1$;                                                                       // (35.7): Atomic block is not pure and does not conform to spec
  if ($pc == PreCommit) {                                                                           
   assume this != Stack.null;                                                                       
  } else {                                                                                          
   assert this != Stack.null;                                                                              // (36.7): Cannot have potential null deference in left-mover part.
  }                                                                                                 
  assume Stack._lock[this] == Tid.null;                                                             
  $pc := transition($pc, _R);                                                                       
  assert $pc != PhaseError;                                                                                // (36.7): Reduction failure
  Stack._lock[this] := tid;                                                                         
  assume Node._state18564_bottom == Node._state && Node.item18564_bottom == Node.item && Node.next18564_bottom == Node.next && Node._lock18564_bottom == Node._lock && Stack._state18564_bottom == Stack._state && Stack.head18564_bottom == Stack.head && Stack._lock18564_bottom == Stack._lock && $result18564_bottom == $result && this18564_bottom == this && tid18564_bottom == tid && $spec$pc.0$18564_bottom == $spec$pc.0$ && $spec$pc.1$18564_bottom == $spec$pc.1$ && $spec$$result18564_bottom == $spec$$result;
  assume $recorded.state18564_bottom == 1;                                                          
  assert phase18564 == $pc;                                                                                // (31.5): Phase must be invariant at loop head
  $spec$Node._state := Node._state;                                                                 
  $spec$Node.item := Node.item;                                                                     
  $spec$Node.next := Node.next;                                                                     
  $spec$Node._lock := Node._lock;                                                                   
  $spec$Stack._state := Stack._state;                                                               
  $spec$Stack.head := Stack.head;                                                                   
  $spec$Stack._lock := Stack._lock;                                                                 
  $spec$$result := $result;                                                                         
 }                                                                                                  
                                                                                                    
 // 38.5: int value;                                                                                
                                                                                                    
                                                                                                    
 // 38.5: Node tmp4;                                                                                
                                                                                                    
                                                                                                    
 // 38.5: tmp4 := this.head;                                                                        
                                                                                                    
                                                                                                    
 moverPath18573 := ReadEval.Stack.head(tid: Tid,this: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 mover18573 := m#moverPath(moverPath18573);                                                         
 path18573 := p#moverPath(moverPath18573);                                                          
 assume Node._state18573 == Node._state && Node.item18573 == Node.item && Node.next18573 == Node.next && Node._lock18573 == Node._lock && Stack._state18573 == Stack._state && Stack.head18573 == Stack.head && Stack._lock18573 == Stack._lock && tmp418573 == tmp4 && value18573 == value && $result18573 == $result && this18573 == this && tid18573 == tid && $pc18573 == $pc && $spec$pc.0$18573 == $spec$pc.0$ && $spec$pc.1$18573 == $spec$pc.1$ && $spec$$result18573 == $spec$$result;
 assume $recorded.state18573 == 1;                                                                  
 if ($pc == PreCommit) {                                                                            
  assume this != Stack.null;                                                                        
 } else {                                                                                           
  assert this != Stack.null;                                                                               // (38.5): Cannot have potential null deference in left-mover part.
 }                                                                                                  
                                                                                                    
 $pc := transition($pc, mover18573);                                                                
 assert $pc != PhaseError;                                                                                 // (38.5): Reduction failure
 tmp4 := Stack.head[this];                                                                          
                                                                                                    
 // 38.5: value := tmp4.item;                                                                       
                                                                                                    
                                                                                                    
 moverPath18576 := ReadEval.Node.item(tid: Tid,tmp4: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 mover18576 := m#moverPath(moverPath18576);                                                         
 path18576 := p#moverPath(moverPath18576);                                                          
 assume Node._state18576 == Node._state && Node.item18576 == Node.item && Node.next18576 == Node.next && Node._lock18576 == Node._lock && Stack._state18576 == Stack._state && Stack.head18576 == Stack.head && Stack._lock18576 == Stack._lock && tmp418576 == tmp4 && value18576 == value && $result18576 == $result && this18576 == this && tid18576 == tid && $pc18576 == $pc && $spec$pc.0$18576 == $spec$pc.0$ && $spec$pc.1$18576 == $spec$pc.1$ && $spec$$result18576 == $spec$$result;
 assume $recorded.state18576 == 1;                                                                  
 if ($pc == PreCommit) {                                                                            
  assume tmp4 != Node.null;                                                                         
 } else {                                                                                           
  assert tmp4 != Node.null;                                                                                // (38.5): Cannot have potential null deference in left-mover part.
 }                                                                                                  
                                                                                                    
 $pc := transition($pc, mover18576);                                                                
 assert $pc != PhaseError;                                                                                 // (38.5): Reduction failure
 value := Node.item[tmp4];                                                                          
                                                                                                    
 // 39.5: Node tmp5;                                                                                
                                                                                                    
                                                                                                    
 // 39.5: Node tmp6;                                                                                
                                                                                                    
                                                                                                    
 // 39.5: tmp6 := this.head;                                                                        
                                                                                                    
                                                                                                    
 moverPath18585 := ReadEval.Stack.head(tid: Tid,this: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 mover18585 := m#moverPath(moverPath18585);                                                         
 path18585 := p#moverPath(moverPath18585);                                                          
 assume Node._state18585 == Node._state && Node.item18585 == Node.item && Node.next18585 == Node.next && Node._lock18585 == Node._lock && Stack._state18585 == Stack._state && Stack.head18585 == Stack.head && Stack._lock18585 == Stack._lock && tmp618585 == tmp6 && tmp518585 == tmp5 && tmp418585 == tmp4 && value18585 == value && $result18585 == $result && this18585 == this && tid18585 == tid && $pc18585 == $pc && $spec$pc.0$18585 == $spec$pc.0$ && $spec$pc.1$18585 == $spec$pc.1$ && $spec$$result18585 == $spec$$result;
 assume $recorded.state18585 == 1;                                                                  
 if ($pc == PreCommit) {                                                                            
  assume this != Stack.null;                                                                        
 } else {                                                                                           
  assert this != Stack.null;                                                                               // (39.5): Cannot have potential null deference in left-mover part.
 }                                                                                                  
                                                                                                    
 $pc := transition($pc, mover18585);                                                                
 assert $pc != PhaseError;                                                                                 // (39.5): Reduction failure
 tmp6 := Stack.head[this];                                                                          
                                                                                                    
 // 39.5: tmp5 := tmp6.next;                                                                        
                                                                                                    
                                                                                                    
 moverPath18588 := ReadEval.Node.next(tid: Tid,tmp6: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 mover18588 := m#moverPath(moverPath18588);                                                         
 path18588 := p#moverPath(moverPath18588);                                                          
 assume Node._state18588 == Node._state && Node.item18588 == Node.item && Node.next18588 == Node.next && Node._lock18588 == Node._lock && Stack._state18588 == Stack._state && Stack.head18588 == Stack.head && Stack._lock18588 == Stack._lock && tmp618588 == tmp6 && tmp518588 == tmp5 && tmp418588 == tmp4 && value18588 == value && $result18588 == $result && this18588 == this && tid18588 == tid && $pc18588 == $pc && $spec$pc.0$18588 == $spec$pc.0$ && $spec$pc.1$18588 == $spec$pc.1$ && $spec$$result18588 == $spec$$result;
 assume $recorded.state18588 == 1;                                                                  
 if ($pc == PreCommit) {                                                                            
  assume tmp6 != Node.null;                                                                         
 } else {                                                                                           
  assert tmp6 != Node.null;                                                                                // (39.5): Cannot have potential null deference in left-mover part.
 }                                                                                                  
                                                                                                    
 $pc := transition($pc, mover18588);                                                                
 assert $pc != PhaseError;                                                                                 // (39.5): Reduction failure
 tmp5 := Node.next[tmp6];                                                                           
                                                                                                    
                                                                                                    
 // 39.5: this.head := tmp5;                                                                        
                                                                                                    
                                                                                                    
 moverPath18591 := WriteEval.Stack.head(tid: Tid,this: Stack,tmp5: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 mover18591 := m#moverPath(moverPath18591);                                                         
 path18591 := p#moverPath(moverPath18591);                                                          
 assume Node._state18591 == Node._state && Node.item18591 == Node.item && Node.next18591 == Node.next && Node._lock18591 == Node._lock && Stack._state18591 == Stack._state && Stack.head18591 == Stack.head && Stack._lock18591 == Stack._lock && tmp618591 == tmp6 && tmp518591 == tmp5 && tmp418591 == tmp4 && value18591 == value && $result18591 == $result && this18591 == this && tid18591 == tid && $pc18591 == $pc && $spec$pc.0$18591 == $spec$pc.0$ && $spec$pc.1$18591 == $spec$pc.1$ && $spec$$result18591 == $spec$$result;
 assume $recorded.state18591 == 1;                                                                  
 if ($pc == PreCommit) {                                                                            
  assume this != Stack.null;                                                                        
 } else {                                                                                           
  assert this != Stack.null;                                                                               // (39.5): Cannot have potential null deference in left-mover part.
 }                                                                                                  
 $pc := transition($pc, mover18591);                                                                
 assert $pc != PhaseError;                                                                                 // (39.5): Reduction failure
 Stack.head[this] := tmp5;                                                                          
 if (isLocal(Node._state[tmp5], tid)) {                                                             
  Node._state[tmp5] := SHARED();                                                                    
  assert isSharedAssignable(Node._state[Node.next[tmp5]]);                                                 // (39.5): tmp5 became shared, but tmp5.next may not be shared.
 }                                                                                                  
                                                                                                    
 if ($pc == PreCommit) {                                                                            
  assume this != Stack.null;                                                                        
 } else {                                                                                           
  assert this != Stack.null;                                                                               // (40.5): Cannot have potential null deference in left-mover part.
 }                                                                                                  
 assert Stack._lock[this] == tid;                                                                          // (40.5): lock not held
 $pc := transition($pc, _L);                                                                        
 assert $pc != PhaseError;                                                                                 // (40.5): Reduction failure
 Stack._lock[this] := Tid.null;                                                                     
                                                                                                    
 // 41.5:  return value;                                                                            
                                                                                                    
 assume Node._state18595 == Node._state && Node.item18595 == Node.item && Node.next18595 == Node.next && Node._lock18595 == Node._lock && Stack._state18595 == Stack._state && Stack.head18595 == Stack.head && Stack._lock18595 == Stack._lock && tmp618595 == tmp6 && tmp518595 == tmp5 && tmp418595 == tmp4 && value18595 == value && $result18595 == $result && this18595 == this && tid18595 == tid && $spec$pc.0$18595 == $spec$pc.0$ && $spec$pc.1$18595 == $spec$pc.1$ && $spec$$result18595 == $spec$$result;
 assume $recorded.state18595 == 1;                                                                  
 $result := value;                                                                                  
                                                                                                    
 call $spec$pc.0$, $spec$pc.1$ :=                                                                   
 Stack.pop.specTransition($spec$pc.0$, $spec$pc.1$, tid,this,$result : int,$spec$$result : int, $spec$Node._state,$spec$Node.item,$spec$Node.next,$spec$Node._lock,$spec$Stack._state,$spec$Stack.head,$spec$Stack._lock,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 assume Node._state18595_post == Node._state && Node.item18595_post == Node.item && Node.next18595_post == Node.next && Node._lock18595_post == Node._lock && Stack._state18595_post == Stack._state && Stack.head18595_post == Stack.head && Stack._lock18595_post == Stack._lock && tmp618595_post == tmp6 && tmp518595_post == tmp5 && tmp418595_post == tmp4 && value18595_post == value && $result18595_post == $result && this18595_post == this && tid18595_post == tid && $spec$pc.0$18595_post == $spec$pc.0$ && $spec$pc.1$18595_post == $spec$pc.1$ && $spec$$result18595_post == $spec$$result;
 assume $recorded.state18595_post == 1;                                                             
 assert $spec$pc.1$;                                                                                       // (41.5): Method returns before completing actions in spec
 return;                                                                                            
                                                                                                    
 // 29.20: // return -1;                                                                            
                                                                                                    
 assume Node._state18599 == Node._state && Node.item18599 == Node.item && Node.next18599 == Node.next && Node._lock18599 == Node._lock && Stack._state18599 == Stack._state && Stack.head18599 == Stack.head && Stack._lock18599 == Stack._lock && tmp618599 == tmp6 && tmp518599 == tmp5 && tmp418599 == tmp4 && value18599 == value && $result18599 == $result && this18599 == this && tid18599 == tid && $spec$pc.0$18599 == $spec$pc.0$ && $spec$pc.1$18599 == $spec$pc.1$ && $spec$$result18599 == $spec$$result;
 assume $recorded.state18599 == 1;                                                                  
 $result := -1;                                                                                     
                                                                                                    
 call $spec$pc.0$, $spec$pc.1$ :=                                                                   
 Stack.pop.specTransition($spec$pc.0$, $spec$pc.1$, tid,this,$result : int,$spec$$result : int, $spec$Node._state,$spec$Node.item,$spec$Node.next,$spec$Node._lock,$spec$Stack._state,$spec$Stack.head,$spec$Stack._lock,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 assume Node._state18599_post == Node._state && Node.item18599_post == Node.item && Node.next18599_post == Node.next && Node._lock18599_post == Node._lock && Stack._state18599_post == Stack._state && Stack.head18599_post == Stack.head && Stack._lock18599_post == Stack._lock && tmp618599_post == tmp6 && tmp518599_post == tmp5 && tmp418599_post == tmp4 && value18599_post == value && $result18599_post == $result && this18599_post == this && tid18599_post == tid && $spec$pc.0$18599_post == $spec$pc.0$ && $spec$pc.1$18599_post == $spec$pc.1$ && $spec$$result18599_post == $spec$$result;
 assume $recorded.state18599_post == 1;                                                             
 assert $spec$pc.1$;                                                                                       // (29.20): Method returns before completing actions in spec
 return;                                                                                            
}                                                                                                   
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
//// Globals                                                                                        
                                                                                                    
                                                                                                    
//// State Invariant                                                                                
                                                                                                    
 function {:inline} StateInvariant(Node._state: [Node]State,Node.item: [Node]int,Node.next: [Node]Node,Node._lock: [Node]Tid,Stack._state: [Stack]State,Stack.head: [Stack]Node,Stack._lock: [Stack]Tid) returns (bool) {
  true &&                                                                                           
  (forall _i: Node  :: _i == Node.null <==> isNull(Node._state[_i])) &&                             
  (forall _i: Stack  :: _i == Stack.null <==> isNull(Stack._state[_i])) &&                          
  (forall _i: Node ::  (isShared(Node._state[_i]) ==> isSharedAssignable(Node._state[Node.next[_i]]))) &&
  (forall _i: Node ::  (forall _t: Tid :: (ValidTid(_t) && isLocal(Node._state[_i],_t) ==> isLocalAssignable(Node._state[Node.next[_i]], _t)))) &&
  (forall _i: Stack ::  (isShared(Stack._state[_i]) ==> isSharedAssignable(Node._state[Stack.head[_i]]))) &&
  (forall _i: Stack ::  (forall _t: Tid :: (ValidTid(_t) && isLocal(Stack._state[_i],_t) ==> isLocalAssignable(Node._state[Stack.head[_i]], _t)))) &&
  _trigger(0) &&                                                                                    
  _trigger(1) &&                                                                                    
  _trigger(2) &&                                                                                    
  _trigger(3)                                                                                       
 }                                                                                                  
//// Spec Checks                                                                                    
                                                                                                    
                                                                                                    
 procedure _CheckWriteWrite.RightMover.Node.item(t: Tid, u: Tid, v: int, w: int, x: Node)           
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[x], u);                                                          
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var w_pre: int;                                                                                    
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
 assume !isError(_writeByT_Mover);                                                                  
 assume leq(_writeByT_Mover,_R);                                                                    
                                                                                                    
 Node.item[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1;                                                                  
 // Do we need to share writeByT.value if it is local?                                              
 _writeByU := WriteEval.Node.item(u: Tid,x: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 assert isError(_writeByU_Mover);                                                                          // (2.3): Node.item failed Write-Write Right-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckWriteRead.RightMover.Node.item(t: Tid, u: Tid, v: int, w: int, x: Node)            
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[x], u);                                                          
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var w_pre: int;                                                                                    
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
 assume !isError(_writeByT_Mover);                                                                  
 assume leq(_writeByT_Mover,_R);                                                                    
                                                                                                    
 Node.item[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1;                                                                  
 // Do we need to share writeByT.value if it is local?                                              
 _readByU := ReadEval.Node.item(u: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 assert _readByU_Mover == _E;                                                                              // (2.3): Node.item failed Write-Read Right-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckWriteWrite.LeftMover.Node.item(t: Tid, u: Tid, v: int, w: int, x: Node)            
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[x], u);                                                          
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var havocValue : int;                                                                              
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var w_pre: int;                                                                                    
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 assume w == Node.item[x];                                                                          
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;  // H                                                             
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
 assume !isError(_writeByT_Mover);                                                                  
 assume leq(_writeByT_Mover,_L);                                                                    
                                                                                                    
                                                                                                    
 Node.item[x] := havocValue;                                                                        
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1;   // H[p.f = _]                                                  
 // Do we need to share writeByT.value if it is local?                                              
 _writeByU := WriteEval.Node.item(u: Tid,x: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 assert isError(_writeByU_Mover);                                                                          // (2.3): Node.item failed Write-Write Left-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckWriteRead.LeftMover.Node.item(t: Tid, u: Tid, v: int, w: int, x: Node)             
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[x], u);                                                          
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var havocValue : int;                                                                              
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var w_pre: int;                                                                                    
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 assume w == Node.item[x];                                                                          
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;  // H                                                             
 _readByU := ReadEval.Node.item(u: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1; // H                                                             
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
 assume !isError(_writeByT_Mover);                                                                  
 assume leq(_writeByT_Mover,_L);                                                                    
                                                                                                    
 assert _readByU_Mover == _E;                                                                              // (2.3): Node.item failed Write-Read Left-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckRead.RightMover.Node.item(t: Tid, u: Tid, v: int, w: int, x: Node)                 
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[x], u);                                                          
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var w_pre: int;                                                                                    
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;  // H                                                             
 _readByT := ReadEval.Node.item(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1;  // H                                                            
 _writeByU := WriteEval.Node.item(u: Tid,x: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 assume leq(_readByT_Mover,_R);                                                                     
                                                                                                    
 assert isError(_writeByU_Mover);                                                                          // (2.3): Node.item failed Read-Write Right-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckRead.LeftMover.Node.item(t: Tid, u: Tid, v: int, w: int, x: Node)                  
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[x], u);                                                          
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var havocValue : int;                                                                              
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var w_pre: int;                                                                                    
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
                                                                                                    
 assume w == Node.item[x];                                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;  // H                                                             
 _readByT := ReadEval.Node.item(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 Node.item[x] := havocValue;                                                                        
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1; // H[p.f := _]                                                   
 _writeByU := WriteEval.Node.item(u: Tid,x: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 assume leq(_readByT_Mover,_L);                                                                     
                                                                                                    
 assert isError(_writeByU_Mover);                                                                          // (2.3): Node.item failed Read-Write Left-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckWriteWrite.RightMover.Node.next(t: Tid, u: Tid, v: Node, w: Node, x: Node)         
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[x], u);                                                          
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
 assume !isError(_writeByT_Mover);                                                                  
 assume leq(_writeByT_Mover,_R);                                                                    
                                                                                                    
 Node.next[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1;                                                                  
 // Do we need to share writeByT.value if it is local?                                              
 _writeByU := WriteEval.Node.next(u: Tid,x: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 assert isError(_writeByU_Mover);                                                                          // (3.3): Node.next failed Write-Write Right-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckWriteRead.RightMover.Node.next(t: Tid, u: Tid, v: Node, w: Node, x: Node)          
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[x], u);                                                          
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
 assume !isError(_writeByT_Mover);                                                                  
 assume leq(_writeByT_Mover,_R);                                                                    
                                                                                                    
 Node.next[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1;                                                                  
 // Do we need to share writeByT.value if it is local?                                              
 _readByU := ReadEval.Node.next(u: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 assert _readByU_Mover == _E;                                                                              // (3.3): Node.next failed Write-Read Right-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckWriteWrite.LeftMover.Node.next(t: Tid, u: Tid, v: Node, w: Node, x: Node)          
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[x], u);                                                          
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var havocValue : Node;                                                                             
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 assume w == Node.next[x];                                                                          
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;  // H                                                             
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
 assume !isError(_writeByT_Mover);                                                                  
 assume leq(_writeByT_Mover,_L);                                                                    
                                                                                                    
                                                                                                    
 Node.next[x] := havocValue;                                                                        
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1;   // H[p.f = _]                                                  
 // Do we need to share writeByT.value if it is local?                                              
 _writeByU := WriteEval.Node.next(u: Tid,x: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 assert isError(_writeByU_Mover);                                                                          // (3.3): Node.next failed Write-Write Left-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckWriteRead.LeftMover.Node.next(t: Tid, u: Tid, v: Node, w: Node, x: Node)           
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[x], u);                                                          
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var havocValue : Node;                                                                             
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 assume w == Node.next[x];                                                                          
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;  // H                                                             
 _readByU := ReadEval.Node.next(u: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1; // H                                                             
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
 assume !isError(_writeByT_Mover);                                                                  
 assume leq(_writeByT_Mover,_L);                                                                    
                                                                                                    
 assert _readByU_Mover == _E;                                                                              // (3.3): Node.next failed Write-Read Left-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckRead.RightMover.Node.next(t: Tid, u: Tid, v: Node, w: Node, x: Node)               
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[x], u);                                                          
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;  // H                                                             
 _readByT := ReadEval.Node.next(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1;  // H                                                            
 _writeByU := WriteEval.Node.next(u: Tid,x: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 assume leq(_readByT_Mover,_R);                                                                     
                                                                                                    
 assert isError(_writeByU_Mover);                                                                          // (3.3): Node.next failed Read-Write Right-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckRead.LeftMover.Node.next(t: Tid, u: Tid, v: Node, w: Node, x: Node)                
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[x], u);                                                          
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var havocValue : Node;                                                                             
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
 assume w == Node.next[x];                                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;  // H                                                             
 _readByT := ReadEval.Node.next(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 Node.next[x] := havocValue;                                                                        
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1; // H[p.f := _]                                                   
 _writeByU := WriteEval.Node.next(u: Tid,x: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 assume leq(_readByT_Mover,_L);                                                                     
                                                                                                    
 assert isError(_writeByU_Mover);                                                                          // (3.3): Node.next failed Read-Write Left-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckWriteWrite.RightMover.Stack.head(t: Tid, u: Tid, v: Node, w: Node, x: Stack)       
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Stack._state[x], u);                                                         
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
 assume !isError(_writeByT_Mover);                                                                  
 assume leq(_writeByT_Mover,_R);                                                                    
                                                                                                    
 Stack.head[x] := v;                                                                                
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1;                                                                  
 // Do we need to share writeByT.value if it is local?                                              
 _writeByU := WriteEval.Stack.head(u: Tid,x: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 assert isError(_writeByU_Mover);                                                                          // (13.3): Stack.head failed Write-Write Right-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckWriteRead.RightMover.Stack.head(t: Tid, u: Tid, v: Node, w: Node, x: Stack)        
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Stack._state[x], u);                                                         
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
 assume !isError(_writeByT_Mover);                                                                  
 assume leq(_writeByT_Mover,_R);                                                                    
                                                                                                    
 Stack.head[x] := v;                                                                                
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1;                                                                  
 // Do we need to share writeByT.value if it is local?                                              
 _readByU := ReadEval.Stack.head(u: Tid,x: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 assert _readByU_Mover == _E;                                                                              // (13.3): Stack.head failed Write-Read Right-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckWriteWrite.LeftMover.Stack.head(t: Tid, u: Tid, v: Node, w: Node, x: Stack)        
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Stack._state[x], u);                                                         
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var havocValue : Node;                                                                             
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 assume w == Stack.head[x];                                                                         
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;  // H                                                             
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
 assume !isError(_writeByT_Mover);                                                                  
 assume leq(_writeByT_Mover,_L);                                                                    
                                                                                                    
                                                                                                    
 Stack.head[x] := havocValue;                                                                       
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1;   // H[p.f = _]                                                  
 // Do we need to share writeByT.value if it is local?                                              
 _writeByU := WriteEval.Stack.head(u: Tid,x: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 assert isError(_writeByU_Mover);                                                                          // (13.3): Stack.head failed Write-Write Left-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckWriteRead.LeftMover.Stack.head(t: Tid, u: Tid, v: Node, w: Node, x: Stack)         
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Stack._state[x], u);                                                         
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var havocValue : Node;                                                                             
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 assume w == Stack.head[x];                                                                         
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;  // H                                                             
 _readByU := ReadEval.Stack.head(u: Tid,x: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1; // H                                                             
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
 assume !isError(_writeByT_Mover);                                                                  
 assume leq(_writeByT_Mover,_L);                                                                    
                                                                                                    
 assert _readByU_Mover == _E;                                                                              // (13.3): Stack.head failed Write-Read Left-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckRead.RightMover.Stack.head(t: Tid, u: Tid, v: Node, w: Node, x: Stack)             
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Stack._state[x], u);                                                         
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;  // H                                                             
 _readByT := ReadEval.Stack.head(t: Tid,x: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1;  // H                                                            
 _writeByU := WriteEval.Stack.head(u: Tid,x: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 assume leq(_readByT_Mover,_R);                                                                     
                                                                                                    
 assert isError(_writeByU_Mover);                                                                          // (13.3): Stack.head failed Read-Write Right-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure _CheckRead.LeftMover.Stack.head(t: Tid, u: Tid, v: Node, w: Node, x: Stack)              
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Stack._state[x], u);                                                         
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var havocValue : Node;                                                                             
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
 assume w == Stack.head[x];                                                                         
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && x_pre == x;
 assume $recorded.state_pre == 1;  // H                                                             
 _readByT := ReadEval.Stack.head(t: Tid,x: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 Stack.head[x] := havocValue;                                                                       
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && x_post == x;
 assume $recorded.state_post == 1; // H[p.f := _]                                                   
 _writeByU := WriteEval.Stack.head(u: Tid,x: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 assume leq(_readByT_Mover,_L);                                                                     
                                                                                                    
 assert isError(_writeByU_Mover);                                                                          // (13.3): Stack.head failed Read-Write Left-Mover Check
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.A.Node.item.Node.item(t: Tid, u: Tid, v: int, w: int, w0: int, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.item;                                                                                
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.item[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _writeByUPost := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _E)) ==> ((_writeByU_Mover == _writeByUPost_Mover || _writeByU_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Node.item (case A.1)
 assert (leq(_writeByT_Mover, _N) && !leq(_writeByUPost_Mover, _L)) ==> (!leq(_writeByU_Mover, _L));       // (2.3): Node.item is not Write-Write Stable with respect to Node.item (case A.2)
 assert (x != y && leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByUPost_Mover == _writeByUPost_Mover || _writeByUPost_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Node.item (case A.3)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 procedure Stable.Check.C.Node.item.Node.item(t: Tid, u: Tid, v: int, w: int, w0: int, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.item;                                                                                
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var tmpV : int;                                                                                    
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var $recorded.state_mid: int;                                                                      
 var w_mid: int;                                                                                    
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var v_mid: int;                                                                                    
 var y_mid: Node;                                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var Node._state_mid: [Node]State;                                                                  
 var x_mid: Node;                                                                                   
 var $pc_mid: Phase;                                                                                
 var w0_mid: int;                                                                                   
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 tmpV := Node.item[x];                                                                              
 Node.item[x] := v;                                                                                 
                                                                                                    
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
 _writeByU := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 Node.item[x] := tmpV;                                                                              
 Node.item[y] := w;                                                                                 
 _writeByTPost := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Node.item (case C)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.DE.Node.item.Node.item(t: Tid, u: Tid, v: int, w: int, w0: int, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.item;                                                                                
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var tmpV : int;                                                                                    
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var $recorded.state_mid: int;                                                                      
 var w_mid: int;                                                                                    
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var v_mid: int;                                                                                    
 var y_mid: Node;                                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var Node._state_mid: [Node]State;                                                                  
 var x_mid: Node;                                                                                   
 var $pc_mid: Phase;                                                                                
 var w0_mid: int;                                                                                   
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 tmpV := Node.item[x];                                                                              
 Node.item[x] := v;                                                                                 
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
                                                                                                    
 _writeByUPost := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
 Node.item[x] := tmpV;                                                                              
 Node.item[y] := w;                                                                                 
 _writeByTPost := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
                                                                                                    
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _N)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Node.item (case D)
 assert (leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Node.item (case R)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.FHI.Node.item.Node.item(t: Tid, u: Tid, v: int, w: int, w0: int, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.item;                                                                                
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _readByTPost : MoverPath;                                                                      
 var _readByTPost_Mover : Mover;                                                                    
 var _readByTPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 _readByT := ReadEval.Node.item(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 _writeByU := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.item[y] := w;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByTPost := ReadEval.Node.item(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByTPost_Mover := m#moverPath(_readByTPost);                                                   
 _readByTPost_Path := p#moverPath(_readByTPost);                                                    
                                                                                                    
 assert (leq(_readByT_Mover, _R) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (2.3): Node.item is not Read-Write Stable with respect to Node.item (case F)
 assert (leq(_readByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (2.3): Node.item is not Read-Write Stable with respect to Node.item (case H)
 assert (x != y && leq(_readByT_Mover, _N) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (2.3): Node.item is not Read-Write Stable with respect to Node.item (case I)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.JKL.Node.item.Node.item(t: Tid, u: Tid, v: int, w: int, w0: int, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.item;                                                                                
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var _readByUPost : MoverPath;                                                                      
 var _readByUPost_Mover : Mover;                                                                    
 var _readByUPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 _readByU := ReadEval.Node.item(u: Tid,y: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.item[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByUPost := ReadEval.Node.item(u: Tid,y: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByUPost_Mover := m#moverPath(_readByUPost);                                                   
 _readByUPost_Path := p#moverPath(_readByUPost);                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_readByUPost_Mover, _E)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (2.3): Node.item is not Write-Read Stable with respect to Node.item (case J)
 assert (leq(_writeByT_Mover, _N) && leq(_readByUPost_Mover, _L)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (2.3): Node.item is not Write-Read Stable with respect to Node.item (case K)
 assert (leq(_writeByT_Mover, _N) && !leq(_readByUPost_Mover, _L)) ==> (!leq(_readByU_Mover, _L));         // (2.3): Node.item is not Write-Read Stable with respect to Node.item (case L)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.A.Node.item.Node.next(t: Tid, u: Tid, v: int, w: Node, w0: Node, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.item;                                                                                
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.item[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _writeByUPost := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _E)) ==> ((_writeByU_Mover == _writeByUPost_Mover || _writeByU_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Node.item (case A.1)
 assert (leq(_writeByT_Mover, _N) && !leq(_writeByUPost_Mover, _L)) ==> (!leq(_writeByU_Mover, _L));       // (3.3): Node.next is not Write-Write Stable with respect to Node.item (case A.2)
 assert (x != y && leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByUPost_Mover == _writeByUPost_Mover || _writeByUPost_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Node.item (case A.3)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 procedure Stable.Check.C.Node.item.Node.next(t: Tid, u: Tid, v: int, w: Node, w0: Node, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.item;                                                                                
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var tmpV : int;                                                                                    
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var w_mid: Node;                                                                                   
 var $recorded.state_mid: int;                                                                      
 var w0_mid: Node;                                                                                  
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var v_mid: int;                                                                                    
 var y_mid: Node;                                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var Node._state_mid: [Node]State;                                                                  
 var x_mid: Node;                                                                                   
 var $pc_mid: Phase;                                                                                
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 tmpV := Node.item[x];                                                                              
 Node.item[x] := v;                                                                                 
                                                                                                    
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
 _writeByU := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 Node.item[x] := tmpV;                                                                              
 Node.next[y] := w;                                                                                 
 _writeByTPost := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Node.next (case C)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.DE.Node.item.Node.next(t: Tid, u: Tid, v: int, w: Node, w0: Node, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.item;                                                                                
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var tmpV : int;                                                                                    
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var w_mid: Node;                                                                                   
 var $recorded.state_mid: int;                                                                      
 var w0_mid: Node;                                                                                  
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var v_mid: int;                                                                                    
 var y_mid: Node;                                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var Node._state_mid: [Node]State;                                                                  
 var x_mid: Node;                                                                                   
 var $pc_mid: Phase;                                                                                
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 tmpV := Node.item[x];                                                                              
 Node.item[x] := v;                                                                                 
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
                                                                                                    
 _writeByUPost := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
 Node.item[x] := tmpV;                                                                              
 Node.next[y] := w;                                                                                 
 _writeByTPost := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
                                                                                                    
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _N)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Node.next (case D)
 assert (leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Node.next (case R)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.FHI.Node.item.Node.next(t: Tid, u: Tid, v: int, w: Node, w0: Node, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.item;                                                                                
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _readByTPost : MoverPath;                                                                      
 var _readByTPost_Mover : Mover;                                                                    
 var _readByTPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _readByT := ReadEval.Node.item(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 _writeByU := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.next[y] := w;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByTPost := ReadEval.Node.item(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByTPost_Mover := m#moverPath(_readByTPost);                                                   
 _readByTPost_Path := p#moverPath(_readByTPost);                                                    
                                                                                                    
 assert (leq(_readByT_Mover, _R) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (2.3): Node.item is not Read-Write Stable with respect to Node.next (case F)
 assert (leq(_readByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (2.3): Node.item is not Read-Write Stable with respect to Node.next (case H)
 assert (x != y && leq(_readByT_Mover, _N) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (2.3): Node.item is not Read-Write Stable with respect to Node.next (case I)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.JKL.Node.item.Node.next(t: Tid, u: Tid, v: int, w: Node, w0: Node, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.item;                                                                                
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var _readByUPost : MoverPath;                                                                      
 var _readByUPost_Mover : Mover;                                                                    
 var _readByUPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _readByU := ReadEval.Node.next(u: Tid,y: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.item[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByUPost := ReadEval.Node.next(u: Tid,y: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByUPost_Mover := m#moverPath(_readByUPost);                                                   
 _readByUPost_Path := p#moverPath(_readByUPost);                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_readByUPost_Mover, _E)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (3.3): Node.next is not Write-Read Stable with respect to Node.item (case J)
 assert (leq(_writeByT_Mover, _N) && leq(_readByUPost_Mover, _L)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (3.3): Node.next is not Write-Read Stable with respect to Node.item (case K)
 assert (leq(_writeByT_Mover, _N) && !leq(_readByUPost_Mover, _L)) ==> (!leq(_readByU_Mover, _L));         // (3.3): Node.next is not Write-Read Stable with respect to Node.item (case L)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.A.Node.item.Stack.head(t: Tid, u: Tid, v: int, w: Node, w0: Node, x: Node, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Node.item;                                                                                
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.item[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _writeByUPost := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _E)) ==> ((_writeByU_Mover == _writeByUPost_Mover || _writeByU_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Node.item (case A.1)
 assert (leq(_writeByT_Mover, _N) && !leq(_writeByUPost_Mover, _L)) ==> (!leq(_writeByU_Mover, _L));       // (13.3): Stack.head is not Write-Write Stable with respect to Node.item (case A.2)
 assert (true && leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByUPost_Mover == _writeByUPost_Mover || _writeByUPost_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Node.item (case A.3)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 procedure Stable.Check.C.Node.item.Stack.head(t: Tid, u: Tid, v: int, w: Node, w0: Node, x: Node, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Node.item;                                                                                
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var tmpV : int;                                                                                    
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var w_mid: Node;                                                                                   
 var $recorded.state_mid: int;                                                                      
 var w0_mid: Node;                                                                                  
 var y_mid: Stack;                                                                                  
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var v_mid: int;                                                                                    
 var Node._lock_mid: [Node]Tid;                                                                     
 var Node._state_mid: [Node]State;                                                                  
 var x_mid: Node;                                                                                   
 var $pc_mid: Phase;                                                                                
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 tmpV := Node.item[x];                                                                              
 Node.item[x] := v;                                                                                 
                                                                                                    
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
 _writeByU := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 Node.item[x] := tmpV;                                                                              
 Stack.head[y] := w;                                                                                
 _writeByTPost := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Stack.head (case C)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.DE.Node.item.Stack.head(t: Tid, u: Tid, v: int, w: Node, w0: Node, x: Node, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Node.item;                                                                                
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var tmpV : int;                                                                                    
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var w_mid: Node;                                                                                   
 var $recorded.state_mid: int;                                                                      
 var w0_mid: Node;                                                                                  
 var y_mid: Stack;                                                                                  
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var v_mid: int;                                                                                    
 var Node._lock_mid: [Node]Tid;                                                                     
 var Node._state_mid: [Node]State;                                                                  
 var x_mid: Node;                                                                                   
 var $pc_mid: Phase;                                                                                
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 tmpV := Node.item[x];                                                                              
 Node.item[x] := v;                                                                                 
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
                                                                                                    
 _writeByUPost := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
 Node.item[x] := tmpV;                                                                              
 Stack.head[y] := w;                                                                                
 _writeByTPost := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
                                                                                                    
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _N)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Stack.head (case D)
 assert (leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Stack.head (case R)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.FHI.Node.item.Stack.head(t: Tid, u: Tid, v: int, w: Node, w0: Node, x: Node, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Node.item;                                                                                
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _readByTPost : MoverPath;                                                                      
 var _readByTPost_Mover : Mover;                                                                    
 var _readByTPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _readByT := ReadEval.Node.item(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 _writeByU := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Stack.head[y] := w;                                                                                
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByTPost := ReadEval.Node.item(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByTPost_Mover := m#moverPath(_readByTPost);                                                   
 _readByTPost_Path := p#moverPath(_readByTPost);                                                    
                                                                                                    
 assert (leq(_readByT_Mover, _R) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (2.3): Node.item is not Read-Write Stable with respect to Stack.head (case F)
 assert (leq(_readByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (2.3): Node.item is not Read-Write Stable with respect to Stack.head (case H)
 assert (true && leq(_readByT_Mover, _N) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (2.3): Node.item is not Read-Write Stable with respect to Stack.head (case I)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.JKL.Node.item.Stack.head(t: Tid, u: Tid, v: int, w: Node, w0: Node, x: Node, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Node.item;                                                                                
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var _readByUPost : MoverPath;                                                                      
 var _readByUPost_Mover : Mover;                                                                    
 var _readByUPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var v_pre: int;                                                                                    
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var v_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _readByU := ReadEval.Stack.head(u: Tid,y: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 _writeByT := WriteEval.Node.item(t: Tid,x: Node,v: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.item[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByUPost := ReadEval.Stack.head(u: Tid,y: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByUPost_Mover := m#moverPath(_readByUPost);                                                   
 _readByUPost_Path := p#moverPath(_readByUPost);                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_readByUPost_Mover, _E)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (13.3): Stack.head is not Write-Read Stable with respect to Node.item (case J)
 assert (leq(_writeByT_Mover, _N) && leq(_readByUPost_Mover, _L)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (13.3): Stack.head is not Write-Read Stable with respect to Node.item (case K)
 assert (leq(_writeByT_Mover, _N) && !leq(_readByUPost_Mover, _L)) ==> (!leq(_readByU_Mover, _L));         // (13.3): Stack.head is not Write-Read Stable with respect to Node.item (case L)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.A.Node.next.Node.item(t: Tid, u: Tid, v: Node, w: int, w0: int, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.next;                                                                                
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.next[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _writeByUPost := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _E)) ==> ((_writeByU_Mover == _writeByUPost_Mover || _writeByU_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Node.next (case A.1)
 assert (leq(_writeByT_Mover, _N) && !leq(_writeByUPost_Mover, _L)) ==> (!leq(_writeByU_Mover, _L));       // (2.3): Node.item is not Write-Write Stable with respect to Node.next (case A.2)
 assert (x != y && leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByUPost_Mover == _writeByUPost_Mover || _writeByUPost_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Node.next (case A.3)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 procedure Stable.Check.C.Node.next.Node.item(t: Tid, u: Tid, v: Node, w: int, w0: int, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.next;                                                                                
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var tmpV : Node;                                                                                   
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var $recorded.state_mid: int;                                                                      
 var v_mid: Node;                                                                                   
 var w_mid: int;                                                                                    
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var y_mid: Node;                                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var Node._state_mid: [Node]State;                                                                  
 var x_mid: Node;                                                                                   
 var $pc_mid: Phase;                                                                                
 var w0_mid: int;                                                                                   
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 tmpV := Node.next[x];                                                                              
 Node.next[x] := v;                                                                                 
                                                                                                    
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
 _writeByU := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 Node.next[x] := tmpV;                                                                              
 Node.item[y] := w;                                                                                 
 _writeByTPost := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Node.item (case C)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.DE.Node.next.Node.item(t: Tid, u: Tid, v: Node, w: int, w0: int, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.next;                                                                                
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var tmpV : Node;                                                                                   
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var $recorded.state_mid: int;                                                                      
 var v_mid: Node;                                                                                   
 var w_mid: int;                                                                                    
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var y_mid: Node;                                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var Node._state_mid: [Node]State;                                                                  
 var x_mid: Node;                                                                                   
 var $pc_mid: Phase;                                                                                
 var w0_mid: int;                                                                                   
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 tmpV := Node.next[x];                                                                              
 Node.next[x] := v;                                                                                 
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
                                                                                                    
 _writeByUPost := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
 Node.next[x] := tmpV;                                                                              
 Node.item[y] := w;                                                                                 
 _writeByTPost := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
                                                                                                    
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _N)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Node.item (case D)
 assert (leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Node.item (case R)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.FHI.Node.next.Node.item(t: Tid, u: Tid, v: Node, w: int, w0: int, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.next;                                                                                
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _readByTPost : MoverPath;                                                                      
 var _readByTPost_Mover : Mover;                                                                    
 var _readByTPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 _readByT := ReadEval.Node.next(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 _writeByU := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.item[y] := w;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByTPost := ReadEval.Node.next(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByTPost_Mover := m#moverPath(_readByTPost);                                                   
 _readByTPost_Path := p#moverPath(_readByTPost);                                                    
                                                                                                    
 assert (leq(_readByT_Mover, _R) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (3.3): Node.next is not Read-Write Stable with respect to Node.item (case F)
 assert (leq(_readByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (3.3): Node.next is not Read-Write Stable with respect to Node.item (case H)
 assert (x != y && leq(_readByT_Mover, _N) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (3.3): Node.next is not Read-Write Stable with respect to Node.item (case I)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.JKL.Node.next.Node.item(t: Tid, u: Tid, v: Node, w: int, w0: int, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.next;                                                                                
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var _readByUPost : MoverPath;                                                                      
 var _readByUPost_Mover : Mover;                                                                    
 var _readByUPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 _readByU := ReadEval.Node.item(u: Tid,y: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.next[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByUPost := ReadEval.Node.item(u: Tid,y: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByUPost_Mover := m#moverPath(_readByUPost);                                                   
 _readByUPost_Path := p#moverPath(_readByUPost);                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_readByUPost_Mover, _E)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (2.3): Node.item is not Write-Read Stable with respect to Node.next (case J)
 assert (leq(_writeByT_Mover, _N) && leq(_readByUPost_Mover, _L)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (2.3): Node.item is not Write-Read Stable with respect to Node.next (case K)
 assert (leq(_writeByT_Mover, _N) && !leq(_readByUPost_Mover, _L)) ==> (!leq(_readByU_Mover, _L));         // (2.3): Node.item is not Write-Read Stable with respect to Node.next (case L)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.A.Node.next.Node.next(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.next;                                                                                
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.next[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _writeByUPost := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _E)) ==> ((_writeByU_Mover == _writeByUPost_Mover || _writeByU_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Node.next (case A.1)
 assert (leq(_writeByT_Mover, _N) && !leq(_writeByUPost_Mover, _L)) ==> (!leq(_writeByU_Mover, _L));       // (3.3): Node.next is not Write-Write Stable with respect to Node.next (case A.2)
 assert (x != y && leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByUPost_Mover == _writeByUPost_Mover || _writeByUPost_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Node.next (case A.3)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 procedure Stable.Check.C.Node.next.Node.next(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.next;                                                                                
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var tmpV : Node;                                                                                   
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var w_mid: Node;                                                                                   
 var $recorded.state_mid: int;                                                                      
 var v_mid: Node;                                                                                   
 var w0_mid: Node;                                                                                  
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var y_mid: Node;                                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var Node._state_mid: [Node]State;                                                                  
 var x_mid: Node;                                                                                   
 var $pc_mid: Phase;                                                                                
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 tmpV := Node.next[x];                                                                              
 Node.next[x] := v;                                                                                 
                                                                                                    
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
 _writeByU := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 Node.next[x] := tmpV;                                                                              
 Node.next[y] := w;                                                                                 
 _writeByTPost := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Node.next (case C)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.DE.Node.next.Node.next(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.next;                                                                                
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var tmpV : Node;                                                                                   
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var w_mid: Node;                                                                                   
 var $recorded.state_mid: int;                                                                      
 var v_mid: Node;                                                                                   
 var w0_mid: Node;                                                                                  
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var y_mid: Node;                                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var Node._state_mid: [Node]State;                                                                  
 var x_mid: Node;                                                                                   
 var $pc_mid: Phase;                                                                                
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 tmpV := Node.next[x];                                                                              
 Node.next[x] := v;                                                                                 
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
                                                                                                    
 _writeByUPost := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
 Node.next[x] := tmpV;                                                                              
 Node.next[y] := w;                                                                                 
 _writeByTPost := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
                                                                                                    
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _N)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Node.next (case D)
 assert (leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Node.next (case R)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.FHI.Node.next.Node.next(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.next;                                                                                
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _readByTPost : MoverPath;                                                                      
 var _readByTPost_Mover : Mover;                                                                    
 var _readByTPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _readByT := ReadEval.Node.next(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 _writeByU := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.next[y] := w;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByTPost := ReadEval.Node.next(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByTPost_Mover := m#moverPath(_readByTPost);                                                   
 _readByTPost_Path := p#moverPath(_readByTPost);                                                    
                                                                                                    
 assert (leq(_readByT_Mover, _R) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (3.3): Node.next is not Read-Write Stable with respect to Node.next (case F)
 assert (leq(_readByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (3.3): Node.next is not Read-Write Stable with respect to Node.next (case H)
 assert (x != y && leq(_readByT_Mover, _N) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (3.3): Node.next is not Read-Write Stable with respect to Node.next (case I)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.JKL.Node.next.Node.next(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Node, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Node._state[y], u);                                                          
 modifies Node.next;                                                                                
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var _readByUPost : MoverPath;                                                                      
 var _readByUPost_Mover : Mover;                                                                    
 var _readByUPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var y_pre: Node;                                                                                   
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _readByU := ReadEval.Node.next(u: Tid,y: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.next[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByUPost := ReadEval.Node.next(u: Tid,y: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByUPost_Mover := m#moverPath(_readByUPost);                                                   
 _readByUPost_Path := p#moverPath(_readByUPost);                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_readByUPost_Mover, _E)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (3.3): Node.next is not Write-Read Stable with respect to Node.next (case J)
 assert (leq(_writeByT_Mover, _N) && leq(_readByUPost_Mover, _L)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (3.3): Node.next is not Write-Read Stable with respect to Node.next (case K)
 assert (leq(_writeByT_Mover, _N) && !leq(_readByUPost_Mover, _L)) ==> (!leq(_readByU_Mover, _L));         // (3.3): Node.next is not Write-Read Stable with respect to Node.next (case L)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.A.Node.next.Stack.head(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Node, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Node.next;                                                                                
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.next[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _writeByUPost := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _E)) ==> ((_writeByU_Mover == _writeByUPost_Mover || _writeByU_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Node.next (case A.1)
 assert (leq(_writeByT_Mover, _N) && !leq(_writeByUPost_Mover, _L)) ==> (!leq(_writeByU_Mover, _L));       // (13.3): Stack.head is not Write-Write Stable with respect to Node.next (case A.2)
 assert (true && leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByUPost_Mover == _writeByUPost_Mover || _writeByUPost_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Node.next (case A.3)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 procedure Stable.Check.C.Node.next.Stack.head(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Node, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Node.next;                                                                                
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var tmpV : Node;                                                                                   
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var w_mid: Node;                                                                                   
 var $recorded.state_mid: int;                                                                      
 var v_mid: Node;                                                                                   
 var w0_mid: Node;                                                                                  
 var y_mid: Stack;                                                                                  
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var Node._state_mid: [Node]State;                                                                  
 var x_mid: Node;                                                                                   
 var $pc_mid: Phase;                                                                                
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 tmpV := Node.next[x];                                                                              
 Node.next[x] := v;                                                                                 
                                                                                                    
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
 _writeByU := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 Node.next[x] := tmpV;                                                                              
 Stack.head[y] := w;                                                                                
 _writeByTPost := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Stack.head (case C)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.DE.Node.next.Stack.head(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Node, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Node.next;                                                                                
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var tmpV : Node;                                                                                   
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var w_mid: Node;                                                                                   
 var $recorded.state_mid: int;                                                                      
 var v_mid: Node;                                                                                   
 var w0_mid: Node;                                                                                  
 var y_mid: Stack;                                                                                  
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var Node._state_mid: [Node]State;                                                                  
 var x_mid: Node;                                                                                   
 var $pc_mid: Phase;                                                                                
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 tmpV := Node.next[x];                                                                              
 Node.next[x] := v;                                                                                 
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
                                                                                                    
 _writeByUPost := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
 Node.next[x] := tmpV;                                                                              
 Stack.head[y] := w;                                                                                
 _writeByTPost := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
                                                                                                    
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _N)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Stack.head (case D)
 assert (leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Stack.head (case R)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.FHI.Node.next.Stack.head(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Node, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Node.next;                                                                                
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _readByTPost : MoverPath;                                                                      
 var _readByTPost_Mover : Mover;                                                                    
 var _readByTPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _readByT := ReadEval.Node.next(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 _writeByU := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Stack.head[y] := w;                                                                                
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByTPost := ReadEval.Node.next(t: Tid,x: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByTPost_Mover := m#moverPath(_readByTPost);                                                   
 _readByTPost_Path := p#moverPath(_readByTPost);                                                    
                                                                                                    
 assert (leq(_readByT_Mover, _R) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (3.3): Node.next is not Read-Write Stable with respect to Stack.head (case F)
 assert (leq(_readByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (3.3): Node.next is not Read-Write Stable with respect to Stack.head (case H)
 assert (true && leq(_readByT_Mover, _N) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (3.3): Node.next is not Read-Write Stable with respect to Stack.head (case I)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.JKL.Node.next.Stack.head(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Node, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Node._state[x], t);                                                          
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Node.next;                                                                                
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var _readByUPost : MoverPath;                                                                      
 var _readByUPost_Mover : Mover;                                                                    
 var _readByUPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var x_pre: Node;                                                                                   
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var x_post: Node;                                                                                  
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _readByU := ReadEval.Stack.head(u: Tid,y: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 _writeByT := WriteEval.Node.next(t: Tid,x: Node,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.next[x] := v;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByUPost := ReadEval.Stack.head(u: Tid,y: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByUPost_Mover := m#moverPath(_readByUPost);                                                   
 _readByUPost_Path := p#moverPath(_readByUPost);                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_readByUPost_Mover, _E)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (13.3): Stack.head is not Write-Read Stable with respect to Node.next (case J)
 assert (leq(_writeByT_Mover, _N) && leq(_readByUPost_Mover, _L)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (13.3): Stack.head is not Write-Read Stable with respect to Node.next (case K)
 assert (leq(_writeByT_Mover, _N) && !leq(_readByUPost_Mover, _L)) ==> (!leq(_readByU_Mover, _L));         // (13.3): Stack.head is not Write-Read Stable with respect to Node.next (case L)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.A.Stack.head.Node.item(t: Tid, u: Tid, v: Node, w: int, w0: int, x: Stack, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Node._state[y], u);                                                          
 modifies Stack.head;                                                                               
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Stack.head[x] := v;                                                                                
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _writeByUPost := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _E)) ==> ((_writeByU_Mover == _writeByUPost_Mover || _writeByU_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Stack.head (case A.1)
 assert (leq(_writeByT_Mover, _N) && !leq(_writeByUPost_Mover, _L)) ==> (!leq(_writeByU_Mover, _L));       // (2.3): Node.item is not Write-Write Stable with respect to Stack.head (case A.2)
 assert (true && leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByUPost_Mover == _writeByUPost_Mover || _writeByUPost_Mover == _E));       // (2.3): Node.item is not Write-Write Stable with respect to Stack.head (case A.3)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 procedure Stable.Check.C.Stack.head.Node.item(t: Tid, u: Tid, v: Node, w: int, w0: int, x: Stack, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Node._state[y], u);                                                          
 modifies Stack.head;                                                                               
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var tmpV : Node;                                                                                   
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var $recorded.state_mid: int;                                                                      
 var v_mid: Node;                                                                                   
 var w_mid: int;                                                                                    
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var y_mid: Node;                                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var x_mid: Stack;                                                                                  
 var Node._state_mid: [Node]State;                                                                  
 var $pc_mid: Phase;                                                                                
 var w0_mid: int;                                                                                   
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 tmpV := Stack.head[x];                                                                             
 Stack.head[x] := v;                                                                                
                                                                                                    
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
 _writeByU := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 Stack.head[x] := tmpV;                                                                             
 Node.item[y] := w;                                                                                 
 _writeByTPost := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Node.item (case C)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.DE.Stack.head.Node.item(t: Tid, u: Tid, v: Node, w: int, w0: int, x: Stack, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Node._state[y], u);                                                          
 modifies Stack.head;                                                                               
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var tmpV : Node;                                                                                   
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var $recorded.state_mid: int;                                                                      
 var v_mid: Node;                                                                                   
 var w_mid: int;                                                                                    
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var y_mid: Node;                                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var x_mid: Stack;                                                                                  
 var Node._state_mid: [Node]State;                                                                  
 var $pc_mid: Phase;                                                                                
 var w0_mid: int;                                                                                   
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 tmpV := Stack.head[x];                                                                             
 Stack.head[x] := v;                                                                                
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
                                                                                                    
 _writeByUPost := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
 Stack.head[x] := tmpV;                                                                             
 Node.item[y] := w;                                                                                 
 _writeByTPost := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
                                                                                                    
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _N)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Node.item (case D)
 assert (leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Node.item (case R)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.FHI.Stack.head.Node.item(t: Tid, u: Tid, v: Node, w: int, w0: int, x: Stack, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Node._state[y], u);                                                          
 modifies Stack.head;                                                                               
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _readByTPost : MoverPath;                                                                      
 var _readByTPost_Mover : Mover;                                                                    
 var _readByTPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 _readByT := ReadEval.Stack.head(t: Tid,x: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 _writeByU := WriteEval.Node.item(u: Tid,y: Node,w: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.item[y] := w;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByTPost := ReadEval.Stack.head(t: Tid,x: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByTPost_Mover := m#moverPath(_readByTPost);                                                   
 _readByTPost_Path := p#moverPath(_readByTPost);                                                    
                                                                                                    
 assert (leq(_readByT_Mover, _R) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (13.3): Stack.head is not Read-Write Stable with respect to Node.item (case F)
 assert (leq(_readByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (13.3): Stack.head is not Read-Write Stable with respect to Node.item (case H)
 assert (true && leq(_readByT_Mover, _N) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (13.3): Stack.head is not Read-Write Stable with respect to Node.item (case I)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.JKL.Stack.head.Node.item(t: Tid, u: Tid, v: Node, w: int, w0: int, x: Stack, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Node._state[y], u);                                                          
 modifies Stack.head;                                                                               
 modifies Node.item;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var _readByUPost : MoverPath;                                                                      
 var _readByUPost_Mover : Mover;                                                                    
 var _readByUPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var w0_pre: int;                                                                                   
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var y_pre: Node;                                                                                   
 var w_pre: int;                                                                                    
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var w0_post: int;                                                                                  
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var Stack._lock_post: [Stack]Tid;                                                                  
 var w_post: int;                                                                                   
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
                                                                                                    
                                                                                                    
 _readByU := ReadEval.Node.item(u: Tid,y: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Stack.head[x] := v;                                                                                
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByUPost := ReadEval.Node.item(u: Tid,y: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByUPost_Mover := m#moverPath(_readByUPost);                                                   
 _readByUPost_Path := p#moverPath(_readByUPost);                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_readByUPost_Mover, _E)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (2.3): Node.item is not Write-Read Stable with respect to Stack.head (case J)
 assert (leq(_writeByT_Mover, _N) && leq(_readByUPost_Mover, _L)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (2.3): Node.item is not Write-Read Stable with respect to Stack.head (case K)
 assert (leq(_writeByT_Mover, _N) && !leq(_readByUPost_Mover, _L)) ==> (!leq(_readByU_Mover, _L));         // (2.3): Node.item is not Write-Read Stable with respect to Stack.head (case L)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.A.Stack.head.Node.next(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Stack, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Node._state[y], u);                                                          
 modifies Stack.head;                                                                               
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var y_pre: Node;                                                                                   
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Stack.head[x] := v;                                                                                
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _writeByUPost := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _E)) ==> ((_writeByU_Mover == _writeByUPost_Mover || _writeByU_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Stack.head (case A.1)
 assert (leq(_writeByT_Mover, _N) && !leq(_writeByUPost_Mover, _L)) ==> (!leq(_writeByU_Mover, _L));       // (3.3): Node.next is not Write-Write Stable with respect to Stack.head (case A.2)
 assert (true && leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByUPost_Mover == _writeByUPost_Mover || _writeByUPost_Mover == _E));       // (3.3): Node.next is not Write-Write Stable with respect to Stack.head (case A.3)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 procedure Stable.Check.C.Stack.head.Node.next(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Stack, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Node._state[y], u);                                                          
 modifies Stack.head;                                                                               
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var tmpV : Node;                                                                                   
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var y_pre: Node;                                                                                   
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var w_mid: Node;                                                                                   
 var $recorded.state_mid: int;                                                                      
 var v_mid: Node;                                                                                   
 var w0_mid: Node;                                                                                  
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var y_mid: Node;                                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var x_mid: Stack;                                                                                  
 var Node._state_mid: [Node]State;                                                                  
 var $pc_mid: Phase;                                                                                
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 tmpV := Stack.head[x];                                                                             
 Stack.head[x] := v;                                                                                
                                                                                                    
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
 _writeByU := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 Stack.head[x] := tmpV;                                                                             
 Node.next[y] := w;                                                                                 
 _writeByTPost := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Node.next (case C)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.DE.Stack.head.Node.next(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Stack, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Node._state[y], u);                                                          
 modifies Stack.head;                                                                               
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var tmpV : Node;                                                                                   
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var y_pre: Node;                                                                                   
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var w_mid: Node;                                                                                   
 var $recorded.state_mid: int;                                                                      
 var v_mid: Node;                                                                                   
 var w0_mid: Node;                                                                                  
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var y_mid: Node;                                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var x_mid: Stack;                                                                                  
 var Node._state_mid: [Node]State;                                                                  
 var $pc_mid: Phase;                                                                                
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 tmpV := Stack.head[x];                                                                             
 Stack.head[x] := v;                                                                                
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
                                                                                                    
 _writeByUPost := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
 Stack.head[x] := tmpV;                                                                             
 Node.next[y] := w;                                                                                 
 _writeByTPost := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
                                                                                                    
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _N)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Node.next (case D)
 assert (leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Node.next (case R)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.FHI.Stack.head.Node.next(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Stack, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Node._state[y], u);                                                          
 modifies Stack.head;                                                                               
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _readByTPost : MoverPath;                                                                      
 var _readByTPost_Mover : Mover;                                                                    
 var _readByTPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var y_pre: Node;                                                                                   
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _readByT := ReadEval.Stack.head(t: Tid,x: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 _writeByU := WriteEval.Node.next(u: Tid,y: Node,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Node.next[y] := w;                                                                                 
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByTPost := ReadEval.Stack.head(t: Tid,x: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByTPost_Mover := m#moverPath(_readByTPost);                                                   
 _readByTPost_Path := p#moverPath(_readByTPost);                                                    
                                                                                                    
 assert (leq(_readByT_Mover, _R) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (13.3): Stack.head is not Read-Write Stable with respect to Node.next (case F)
 assert (leq(_readByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (13.3): Stack.head is not Read-Write Stable with respect to Node.next (case H)
 assert (true && leq(_readByT_Mover, _N) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (13.3): Stack.head is not Read-Write Stable with respect to Node.next (case I)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.JKL.Stack.head.Node.next(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Stack, y: Node)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Node._state[y], u);                                                          
 modifies Stack.head;                                                                               
 modifies Node.next;                                                                                
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var _readByUPost : MoverPath;                                                                      
 var _readByUPost_Mover : Mover;                                                                    
 var _readByUPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var y_pre: Node;                                                                                   
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Node;                                                                                  
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _readByU := ReadEval.Node.next(u: Tid,y: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Stack.head[x] := v;                                                                                
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByUPost := ReadEval.Node.next(u: Tid,y: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByUPost_Mover := m#moverPath(_readByUPost);                                                   
 _readByUPost_Path := p#moverPath(_readByUPost);                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_readByUPost_Mover, _E)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (3.3): Node.next is not Write-Read Stable with respect to Stack.head (case J)
 assert (leq(_writeByT_Mover, _N) && leq(_readByUPost_Mover, _L)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (3.3): Node.next is not Write-Read Stable with respect to Stack.head (case K)
 assert (leq(_writeByT_Mover, _N) && !leq(_readByUPost_Mover, _L)) ==> (!leq(_readByU_Mover, _L));         // (3.3): Node.next is not Write-Read Stable with respect to Stack.head (case L)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.A.Stack.head.Stack.head(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Stack, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Stack.head;                                                                               
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Stack.head[x] := v;                                                                                
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _writeByUPost := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _E)) ==> ((_writeByU_Mover == _writeByUPost_Mover || _writeByU_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Stack.head (case A.1)
 assert (leq(_writeByT_Mover, _N) && !leq(_writeByUPost_Mover, _L)) ==> (!leq(_writeByU_Mover, _L));       // (13.3): Stack.head is not Write-Write Stable with respect to Stack.head (case A.2)
 assert (x != y && leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByUPost_Mover == _writeByUPost_Mover || _writeByUPost_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Stack.head (case A.3)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 procedure Stable.Check.C.Stack.head.Stack.head(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Stack, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Stack.head;                                                                               
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var tmpV : Node;                                                                                   
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var w_mid: Node;                                                                                   
 var $recorded.state_mid: int;                                                                      
 var v_mid: Node;                                                                                   
 var w0_mid: Node;                                                                                  
 var y_mid: Stack;                                                                                  
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var x_mid: Stack;                                                                                  
 var Node._state_mid: [Node]State;                                                                  
 var $pc_mid: Phase;                                                                                
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 tmpV := Stack.head[x];                                                                             
 Stack.head[x] := v;                                                                                
                                                                                                    
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
 _writeByU := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 Stack.head[x] := tmpV;                                                                             
 Stack.head[y] := w;                                                                                
 _writeByTPost := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Stack.head (case C)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.DE.Stack.head.Stack.head(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Stack, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Stack.head;                                                                               
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var tmpV : Node;                                                                                   
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _writeByUPost : MoverPath;                                                                     
 var _writeByUPost_Mover : Mover;                                                                   
 var _writeByUPost_Path : int;                                                                      
 var _writeByTPost : MoverPath;                                                                     
 var _writeByTPost_Mover : Mover;                                                                   
 var _writeByTPost_Path : int;                                                                      
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_mid: [Stack]Node;                                                                   
 var Stack._state_mid: [Stack]State;                                                                
 var Node.next_mid: [Node]Node;                                                                     
 var t_mid: Tid;                                                                                    
 var u_mid: Tid;                                                                                    
 var w_mid: Node;                                                                                   
 var $recorded.state_mid: int;                                                                      
 var v_mid: Node;                                                                                   
 var w0_mid: Node;                                                                                  
 var y_mid: Stack;                                                                                  
 var Stack._lock_mid: [Stack]Tid;                                                                   
 var Node._lock_mid: [Node]Tid;                                                                     
 var x_mid: Stack;                                                                                  
 var Node._state_mid: [Node]State;                                                                  
 var $pc_mid: Phase;                                                                                
 var Node.item_mid: [Node]int;                                                                      
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _writeByU := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 tmpV := Stack.head[x];                                                                             
 Stack.head[x] := v;                                                                                
 assume Node._state_mid == Node._state && Node.item_mid == Node.item && Node.next_mid == Node.next && Node._lock_mid == Node._lock && Stack._state_mid == Stack._state && Stack.head_mid == Stack.head && Stack._lock_mid == Stack._lock && t_mid == t && u_mid == u && v_mid == v && w_mid == w && w0_mid == w0 && x_mid == x && y_mid == y;
 assume $recorded.state_mid == 1;                                                                   
                                                                                                    
 _writeByUPost := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByUPost_Mover := m#moverPath(_writeByUPost);                                                 
 _writeByUPost_Path := p#moverPath(_writeByUPost);                                                  
                                                                                                    
 Stack.head[x] := tmpV;                                                                             
 Stack.head[y] := w;                                                                                
 _writeByTPost := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByTPost_Mover := m#moverPath(_writeByTPost);                                                 
 _writeByTPost_Path := p#moverPath(_writeByTPost);                                                  
                                                                                                    
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_writeByUPost_Mover, _N)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Stack.head (case D)
 assert (leq(_writeByT_Mover, _N) && leq(_writeByUPost_Mover, _L)) ==> ((_writeByTPost_Mover == _writeByT_Mover || _writeByTPost_Mover == _E));       // (13.3): Stack.head is not Write-Write Stable with respect to Stack.head (case R)
                                                                                                    
 }                                                                                                  
                                                                                                    
                                                                                                    
 procedure Stable.Check.FHI.Stack.head.Stack.head(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Stack, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Stack.head;                                                                               
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _writeByU : MoverPath;                                                                         
 var _writeByU_Mover : Mover;                                                                       
 var _writeByU_Path : int;                                                                          
 var _readByT : MoverPath;                                                                          
 var _readByT_Mover : Mover;                                                                        
 var _readByT_Path : int;                                                                           
 var _readByTPost : MoverPath;                                                                      
 var _readByTPost_Mover : Mover;                                                                    
 var _readByTPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _readByT := ReadEval.Stack.head(t: Tid,x: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByT_Mover := m#moverPath(_readByT);                                                           
 _readByT_Path := p#moverPath(_readByT);                                                            
 _writeByU := WriteEval.Stack.head(u: Tid,y: Stack,w: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByU_Mover := m#moverPath(_writeByU);                                                         
 _writeByU_Path := p#moverPath(_writeByU);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Stack.head[y] := w;                                                                                
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByTPost := ReadEval.Stack.head(t: Tid,x: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByTPost_Mover := m#moverPath(_readByTPost);                                                   
 _readByTPost_Path := p#moverPath(_readByTPost);                                                    
                                                                                                    
 assert (leq(_readByT_Mover, _R) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (13.3): Stack.head is not Read-Write Stable with respect to Stack.head (case F)
 assert (leq(_readByT_Mover, _E) && leq(_writeByU_Mover, _L)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (13.3): Stack.head is not Read-Write Stable with respect to Stack.head (case H)
 assert (x != y && leq(_readByT_Mover, _N) && leq(_writeByU_Mover, _N)) ==> ((_readByTPost_Mover == _readByT_Mover || _readByTPost_Mover == _E));       // (13.3): Stack.head is not Read-Write Stable with respect to Stack.head (case I)
                                                                                                    
 }                                                                                                  
                                                                                                    
 procedure Stable.Check.JKL.Stack.head.Stack.head(t: Tid, u: Tid, v: Node, w: Node, w0: Node, x: Stack, y: Stack)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(t);                                                                              
 requires ValidTid(u);                                                                              
 requires t != u;                                                                                   
 requires isAccessible(Stack._state[x], t);                                                         
 requires isAccessible(Stack._state[y], u);                                                         
 modifies Stack.head;                                                                               
 modifies Stack.head;                                                                               
                                                                                                    
 {                                                                                                  
 var _writeByT : MoverPath;                                                                         
 var _writeByT_Mover : Mover;                                                                       
 var _writeByT_Path : int;                                                                          
 var _readByU : MoverPath;                                                                          
 var _readByU_Mover : Mover;                                                                        
 var _readByU_Path : int;                                                                           
 var _readByUPost : MoverPath;                                                                      
 var _readByUPost_Mover : Mover;                                                                    
 var _readByUPost_Path : int;                                                                       
 var Node._lock_pre: [Node]Tid;                                                                     
 var $recorded.state_pre: int;                                                                      
 var u_pre: Tid;                                                                                    
 var Node._state_pre: [Node]State;                                                                  
 var x_pre: Stack;                                                                                  
 var v_pre: Node;                                                                                   
 var Stack._lock_pre: [Stack]Tid;                                                                   
 var $pc_pre: Phase;                                                                                
 var w0_pre: Node;                                                                                  
 var w_pre: Node;                                                                                   
 var Node.next_pre: [Node]Node;                                                                     
 var Stack._state_pre: [Stack]State;                                                                
 var Stack.head_pre: [Stack]Node;                                                                   
 var Node.item_pre: [Node]int;                                                                      
 var t_pre: Tid;                                                                                    
 var y_pre: Stack;                                                                                  
                                                                                                    
 var Stack.head_post: [Stack]Node;                                                                  
 var y_post: Stack;                                                                                 
 var Stack._state_post: [Stack]State;                                                               
 var $recorded.state_post: int;                                                                     
 var Node.item_post: [Node]int;                                                                     
 var t_post: Tid;                                                                                   
 var $pc_post: Phase;                                                                               
 var Node._lock_post: [Node]Tid;                                                                    
 var w0_post: Node;                                                                                 
 var Stack._lock_post: [Stack]Tid;                                                                  
 var Node._state_post: [Node]State;                                                                 
 var Node.next_post: [Node]Node;                                                                    
 var x_post: Stack;                                                                                 
 var v_post: Node;                                                                                  
 var u_post: Tid;                                                                                   
 var w_post: Node;                                                                                  
                                                                                                    
                                                                                                    
 _readByU := ReadEval.Stack.head(u: Tid,y: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByU_Mover := m#moverPath(_readByU);                                                           
 _readByU_Path := p#moverPath(_readByU);                                                            
 _writeByT := WriteEval.Stack.head(t: Tid,x: Stack,v: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _writeByT_Mover := m#moverPath(_writeByT);                                                         
 _writeByT_Path := p#moverPath(_writeByT);                                                          
                                                                                                    
 assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && t_pre == t && u_pre == u && v_pre == v && w_pre == w && w0_pre == w0 && x_pre == x && y_pre == y;
 assume $recorded.state_pre == 1;                                                                   
 Stack.head[x] := v;                                                                                
 assume Node._state_post == Node._state && Node.item_post == Node.item && Node.next_post == Node.next && Node._lock_post == Node._lock && Stack._state_post == Stack._state && Stack.head_post == Stack.head && Stack._lock_post == Stack._lock && t_post == t && u_post == u && v_post == v && w_post == w && w0_post == w0 && x_post == x && y_post == y;
 assume $recorded.state_post == 1;                                                                  
                                                                                                    
 _readByUPost := ReadEval.Stack.head(u: Tid,y: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock);
 _readByUPost_Mover := m#moverPath(_readByUPost);                                                   
 _readByUPost_Path := p#moverPath(_readByUPost);                                                    
                                                                                                    
 assert (leq(_writeByT_Mover, _R) && leq(_readByUPost_Mover, _E)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (13.3): Stack.head is not Write-Read Stable with respect to Stack.head (case J)
 assert (leq(_writeByT_Mover, _N) && leq(_readByUPost_Mover, _L)) ==> ((_readByU_Mover == _readByUPost_Mover || _readByU_Mover == _E));       // (13.3): Stack.head is not Write-Read Stable with respect to Stack.head (case K)
 assert (leq(_writeByT_Mover, _N) && !leq(_readByUPost_Mover, _L)) ==> (!leq(_readByU_Mover, _L));         // (13.3): Stack.head is not Write-Read Stable with respect to Stack.head (case L)
                                                                                                    
 }                                                                                                  
                                                                                                    
procedure Yield(tid: Tid);                                                                          
requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
requires ValidTid(tid);                                                                             
modifies Node._state;                                                                               
modifies Node.item;                                                                                 
modifies Node.next;                                                                                 
modifies Node._lock;                                                                                
modifies Stack._state;                                                                              
modifies Stack.head;                                                                                
modifies Stack._lock;                                                                               
ensures StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
ensures Y(tid , old(Node._state), old(Node.item), old(Node.next), old(Node._lock), old(Stack._state), old(Stack.head), old(Stack._lock) , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
                                                                                                    
// Node.item:                                                                                       
                                                                                                    
function {:inline} Y_Node.item(tid : Tid, this: Node, newValue: int , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid): bool
{                                                                                                   
 ((isAccessible(Node._state[this], tid) && leq(m#moverPath(ReadEval.Node.item(tid: Tid,this: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)), _R)) ==> (Node.item[this] == newValue))
                                                                                                    
}                                                                                                   
                                                                                                    
function {:inline} Invariant.Y_Node.item(tid : Tid, this: Node, newValue: int , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid): bool
{                                                                                                   
 true                                                                                               
                                                                                                    
}                                                                                                   
                                                                                                    
procedure Y_Node.item.Subsumes.W(tid : Tid, u : Tid, this: Node, newValue: int , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(tid);                                                                            
 requires ValidTid(u) && u != tid;                                                                  
                                                                                                    
{                                                                                                   
var Node.next_yield: [Node]Node;                                                                    
var Stack._lock_yield: [Stack]Tid;                                                                  
var this_yield: Node;                                                                               
var Node.item_yield: [Node]int;                                                                     
var Node._state_yield: [Node]State;                                                                 
var tid_yield: Tid;                                                                                 
var $pc_yield: Phase;                                                                               
var newValue_yield: int;                                                                            
var u_yield: Tid;                                                                                   
var Stack.head_yield: [Stack]Node;                                                                  
var Node._lock_yield: [Node]Tid;                                                                    
var Stack._state_yield: [Stack]State;                                                               
var $recorded.state_yield: int;                                                                     
                                                                                                    
 assume isAccessible(Node._state[this], tid);                                                       
 assume isAccessible(Node._state[this], u);                                                         
 assume !isError(m#moverPath(WriteEval.Node.item(u: Tid,this: Node,newValue: int,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)));
                                                                                                    
assume Node._state_yield == Node._state && Node.item_yield == Node.item && Node.next_yield == Node.next && Node._lock_yield == Node._lock && Stack._state_yield == Stack._state && Stack.head_yield == Stack.head && Stack._lock_yield == Stack._lock && u_yield == u && newValue_yield == newValue && this_yield == this && tid_yield == tid;
assume $recorded.state_yield == 1;                                                                  
 assert Y_Node.item(tid, this, newValue , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
                                                                                                    
procedure Y_Node.item.Reflexive(tid : Tid, this: Node , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(tid);                                                                            
                                                                                                    
{                                                                                                   
var Node.next_yield: [Node]Node;                                                                    
var Stack._lock_yield: [Stack]Tid;                                                                  
var this_yield: Node;                                                                               
var Node.item_yield: [Node]int;                                                                     
var Node._state_yield: [Node]State;                                                                 
var tid_yield: Tid;                                                                                 
var $pc_yield: Phase;                                                                               
var Stack.head_yield: [Stack]Node;                                                                  
var Node._lock_yield: [Node]Tid;                                                                    
var Stack._state_yield: [Stack]State;                                                               
var $recorded.state_yield: int;                                                                     
                                                                                                    
 assume isAccessible(Node._state[this], tid);                                                       
assume Node._state_yield == Node._state && Node.item_yield == Node.item && Node.next_yield == Node.next && Node._lock_yield == Node._lock && Stack._state_yield == Stack._state && Stack.head_yield == Stack.head && Stack._lock_yield == Stack._lock && this_yield == this && tid_yield == tid;
assume $recorded.state_yield == 1;                                                                  
 assert Y_Node.item(tid, this, Node.item[this] , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
                                                                                                    
procedure Y_Node.item.Transitive(tid : Tid, this: Node, newValue : int , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid , Node._state_p: [Node]State, Node.item_p: [Node]int, Node.next_p: [Node]Node, Node._lock_p: [Node]Tid, Stack._state_p: [Stack]State, Stack.head_p: [Stack]Node, Stack._lock_p: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires StateInvariant(Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
 requires ValidTid(tid);                                                                            
                                                                                                    
{                                                                                                   
var Node._lock_pre: [Node]Tid;                                                                      
var $recorded.state_pre: int;                                                                       
var this_pre: Node;                                                                                 
var newValue_pre: int;                                                                              
var Node._state_pre: [Node]State;                                                                   
var tid_pre: Tid;                                                                                   
var Stack._lock_pre: [Stack]Tid;                                                                    
var $pc_pre: Phase;                                                                                 
var Node.next_pre: [Node]Node;                                                                      
var Stack._state_pre: [Stack]State;                                                                 
var Stack.head_pre: [Stack]Node;                                                                    
var Node.item_pre: [Node]int;                                                                       
                                                                                                    
var Stack.head_post: [Stack]Node;                                                                   
var Stack._state_post: [Stack]State;                                                                
var $recorded.state_post: int;                                                                      
var Node.item_post: [Node]int;                                                                      
var newValue_post: int;                                                                             
var $pc_post: Phase;                                                                                
var Node._lock_post: [Node]Tid;                                                                     
var tid_post: Tid;                                                                                  
var Stack._lock_post: [Stack]Tid;                                                                   
var Node._state_post: [Node]State;                                                                  
var Node.next_post: [Node]Node;                                                                     
var this_post: Node;                                                                                
                                                                                                    
assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && newValue_pre == newValue && this_pre == this && tid_pre == tid;
assume $recorded.state_pre == 1;                                                                    
 assume isAccessible(Node._state[this], tid);                                                       
 assume Y(tid , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock , Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
 assume Y_Node.item(tid, this, newValue , Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
assume Node._state_post == Node._state_p && Node.item_post == Node.item_p && Node.next_post == Node.next_p && Node._lock_post == Node._lock_p && Stack._state_post == Stack._state_p && Stack.head_post == Stack.head_p && Stack._lock_post == Stack._lock_p && newValue_post == newValue && this_post == this && tid_post == tid;
assume $recorded.state_post == 1;                                                                   
 assert Y_Node.item(tid, this, newValue , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
// Node.next:                                                                                       
                                                                                                    
function {:inline} Y_Node.next(tid : Tid, this: Node, newValue: Node , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid): bool
{                                                                                                   
 ((isAccessible(Node._state[this], tid) && leq(m#moverPath(ReadEval.Node.next(tid: Tid,this: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)), _R)) ==> (Node.next[this] == newValue))
                                                                                                    
}                                                                                                   
                                                                                                    
function {:inline} Invariant.Y_Node.next(tid : Tid, this: Node, newValue: Node , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid): bool
{                                                                                                   
 true                                                                                               
                                                                                                    
}                                                                                                   
                                                                                                    
procedure Y_Node.next.Subsumes.W(tid : Tid, u : Tid, this: Node, newValue: Node , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(tid);                                                                            
 requires ValidTid(u) && u != tid;                                                                  
                                                                                                    
{                                                                                                   
var Node.next_yield: [Node]Node;                                                                    
var Stack._lock_yield: [Stack]Tid;                                                                  
var this_yield: Node;                                                                               
var Node.item_yield: [Node]int;                                                                     
var Node._state_yield: [Node]State;                                                                 
var tid_yield: Tid;                                                                                 
var $pc_yield: Phase;                                                                               
var u_yield: Tid;                                                                                   
var Stack.head_yield: [Stack]Node;                                                                  
var Node._lock_yield: [Node]Tid;                                                                    
var newValue_yield: Node;                                                                           
var Stack._state_yield: [Stack]State;                                                               
var $recorded.state_yield: int;                                                                     
                                                                                                    
 assume isAccessible(Node._state[this], tid);                                                       
 assume isAccessible(Node._state[this], u);                                                         
 assume !isError(m#moverPath(WriteEval.Node.next(u: Tid,this: Node,newValue: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)));
                                                                                                    
assume Node._state_yield == Node._state && Node.item_yield == Node.item && Node.next_yield == Node.next && Node._lock_yield == Node._lock && Stack._state_yield == Stack._state && Stack.head_yield == Stack.head && Stack._lock_yield == Stack._lock && u_yield == u && newValue_yield == newValue && this_yield == this && tid_yield == tid;
assume $recorded.state_yield == 1;                                                                  
 assert Y_Node.next(tid, this, newValue , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
                                                                                                    
procedure Y_Node.next.Reflexive(tid : Tid, this: Node , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(tid);                                                                            
                                                                                                    
{                                                                                                   
var Node.next_yield: [Node]Node;                                                                    
var Stack._lock_yield: [Stack]Tid;                                                                  
var this_yield: Node;                                                                               
var Node.item_yield: [Node]int;                                                                     
var Node._state_yield: [Node]State;                                                                 
var tid_yield: Tid;                                                                                 
var $pc_yield: Phase;                                                                               
var Stack.head_yield: [Stack]Node;                                                                  
var Node._lock_yield: [Node]Tid;                                                                    
var Stack._state_yield: [Stack]State;                                                               
var $recorded.state_yield: int;                                                                     
                                                                                                    
 assume isAccessible(Node._state[this], tid);                                                       
assume Node._state_yield == Node._state && Node.item_yield == Node.item && Node.next_yield == Node.next && Node._lock_yield == Node._lock && Stack._state_yield == Stack._state && Stack.head_yield == Stack.head && Stack._lock_yield == Stack._lock && this_yield == this && tid_yield == tid;
assume $recorded.state_yield == 1;                                                                  
 assert Y_Node.next(tid, this, Node.next[this] , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
                                                                                                    
procedure Y_Node.next.Transitive(tid : Tid, this: Node, newValue : Node , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid , Node._state_p: [Node]State, Node.item_p: [Node]int, Node.next_p: [Node]Node, Node._lock_p: [Node]Tid, Stack._state_p: [Stack]State, Stack.head_p: [Stack]Node, Stack._lock_p: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires StateInvariant(Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
 requires ValidTid(tid);                                                                            
                                                                                                    
{                                                                                                   
var newValue_pre: Node;                                                                             
var Node._lock_pre: [Node]Tid;                                                                      
var $recorded.state_pre: int;                                                                       
var this_pre: Node;                                                                                 
var Node._state_pre: [Node]State;                                                                   
var tid_pre: Tid;                                                                                   
var Stack._lock_pre: [Stack]Tid;                                                                    
var $pc_pre: Phase;                                                                                 
var Node.next_pre: [Node]Node;                                                                      
var Stack._state_pre: [Stack]State;                                                                 
var Stack.head_pre: [Stack]Node;                                                                    
var Node.item_pre: [Node]int;                                                                       
                                                                                                    
var Stack.head_post: [Stack]Node;                                                                   
var Stack._state_post: [Stack]State;                                                                
var $recorded.state_post: int;                                                                      
var newValue_post: Node;                                                                            
var Node.item_post: [Node]int;                                                                      
var $pc_post: Phase;                                                                                
var Node._lock_post: [Node]Tid;                                                                     
var tid_post: Tid;                                                                                  
var Stack._lock_post: [Stack]Tid;                                                                   
var Node._state_post: [Node]State;                                                                  
var Node.next_post: [Node]Node;                                                                     
var this_post: Node;                                                                                
                                                                                                    
assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && newValue_pre == newValue && this_pre == this && tid_pre == tid;
assume $recorded.state_pre == 1;                                                                    
 assume isAccessible(Node._state[this], tid);                                                       
 assume Y(tid , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock , Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
 assume Y_Node.next(tid, this, newValue , Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
assume Node._state_post == Node._state_p && Node.item_post == Node.item_p && Node.next_post == Node.next_p && Node._lock_post == Node._lock_p && Stack._state_post == Stack._state_p && Stack.head_post == Stack.head_p && Stack._lock_post == Stack._lock_p && newValue_post == newValue && this_post == this && tid_post == tid;
assume $recorded.state_post == 1;                                                                   
 assert Y_Node.next(tid, this, newValue , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
// Node._lock:                                                                                      
                                                                                                    
function {:inline} Y_Node._lock(tid : Tid, this: Node, newValue: Tid , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid): bool
{                                                                                                   
 ((isAccessible(Node._state[this], tid) && leq(m#moverPath(ReadEval.Node._lock(tid: Tid,this: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)), _R)) ==> (Node._lock[this] == newValue))
 &&(((Node._lock[this]==tid)==(newValue==tid)))                                                     
                                                                                                    
}                                                                                                   
                                                                                                    
function {:inline} Invariant.Y_Node._lock(tid : Tid, this: Node, newValue: Tid , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid): bool
{                                                                                                   
 true                                                                                               
                                                                                                    
}                                                                                                   
                                                                                                    
procedure Y_Node._lock.Subsumes.W(tid : Tid, u : Tid, this: Node, newValue: Tid , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(tid);                                                                            
 requires ValidTid(u) && u != tid;                                                                  
                                                                                                    
{                                                                                                   
var Node.next_yield: [Node]Node;                                                                    
var Stack._lock_yield: [Stack]Tid;                                                                  
var this_yield: Node;                                                                               
var Node.item_yield: [Node]int;                                                                     
var newValue_yield: Tid;                                                                            
var Node._state_yield: [Node]State;                                                                 
var tid_yield: Tid;                                                                                 
var $pc_yield: Phase;                                                                               
var u_yield: Tid;                                                                                   
var Stack.head_yield: [Stack]Node;                                                                  
var Node._lock_yield: [Node]Tid;                                                                    
var Stack._state_yield: [Stack]State;                                                               
var $recorded.state_yield: int;                                                                     
                                                                                                    
 assume isAccessible(Node._state[this], tid);                                                       
 assume isAccessible(Node._state[this], u);                                                         
 assume !isError(m#moverPath(WriteEval.Node._lock(u: Tid,this: Node,newValue: Tid,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)));
 assume leq(m#moverPath(ReadEval.Node._lock(tid: Tid,this: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)), _N);
assume Node._state_yield == Node._state && Node.item_yield == Node.item && Node.next_yield == Node.next && Node._lock_yield == Node._lock && Stack._state_yield == Stack._state && Stack.head_yield == Stack.head && Stack._lock_yield == Stack._lock && u_yield == u && newValue_yield == newValue && this_yield == this && tid_yield == tid;
assume $recorded.state_yield == 1;                                                                  
 assert Y_Node._lock(tid, this, newValue , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
                                                                                                    
procedure Y_Node._lock.Reflexive(tid : Tid, this: Node , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(tid);                                                                            
                                                                                                    
{                                                                                                   
var Node.next_yield: [Node]Node;                                                                    
var Stack._lock_yield: [Stack]Tid;                                                                  
var this_yield: Node;                                                                               
var Node.item_yield: [Node]int;                                                                     
var Node._state_yield: [Node]State;                                                                 
var tid_yield: Tid;                                                                                 
var $pc_yield: Phase;                                                                               
var Stack.head_yield: [Stack]Node;                                                                  
var Node._lock_yield: [Node]Tid;                                                                    
var Stack._state_yield: [Stack]State;                                                               
var $recorded.state_yield: int;                                                                     
                                                                                                    
 assume isAccessible(Node._state[this], tid);                                                       
assume Node._state_yield == Node._state && Node.item_yield == Node.item && Node.next_yield == Node.next && Node._lock_yield == Node._lock && Stack._state_yield == Stack._state && Stack.head_yield == Stack.head && Stack._lock_yield == Stack._lock && this_yield == this && tid_yield == tid;
assume $recorded.state_yield == 1;                                                                  
 assert Y_Node._lock(tid, this, Node._lock[this] , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
                                                                                                    
procedure Y_Node._lock.Transitive(tid : Tid, this: Node, newValue : Tid , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid , Node._state_p: [Node]State, Node.item_p: [Node]int, Node.next_p: [Node]Node, Node._lock_p: [Node]Tid, Stack._state_p: [Stack]State, Stack.head_p: [Stack]Node, Stack._lock_p: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires StateInvariant(Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
 requires ValidTid(tid);                                                                            
                                                                                                    
{                                                                                                   
var Node._lock_pre: [Node]Tid;                                                                      
var $recorded.state_pre: int;                                                                       
var this_pre: Node;                                                                                 
var Node._state_pre: [Node]State;                                                                   
var tid_pre: Tid;                                                                                   
var Stack._lock_pre: [Stack]Tid;                                                                    
var $pc_pre: Phase;                                                                                 
var Node.next_pre: [Node]Node;                                                                      
var Stack._state_pre: [Stack]State;                                                                 
var Stack.head_pre: [Stack]Node;                                                                    
var newValue_pre: Tid;                                                                              
var Node.item_pre: [Node]int;                                                                       
                                                                                                    
var Stack.head_post: [Stack]Node;                                                                   
var Stack._state_post: [Stack]State;                                                                
var $recorded.state_post: int;                                                                      
var Node.item_post: [Node]int;                                                                      
var $pc_post: Phase;                                                                                
var Node._lock_post: [Node]Tid;                                                                     
var tid_post: Tid;                                                                                  
var Stack._lock_post: [Stack]Tid;                                                                   
var Node._state_post: [Node]State;                                                                  
var Node.next_post: [Node]Node;                                                                     
var this_post: Node;                                                                                
var newValue_post: Tid;                                                                             
                                                                                                    
assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && newValue_pre == newValue && this_pre == this && tid_pre == tid;
assume $recorded.state_pre == 1;                                                                    
 assume isAccessible(Node._state[this], tid);                                                       
 assume Y(tid , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock , Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
 assume Y_Node._lock(tid, this, newValue , Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
assume Node._state_post == Node._state_p && Node.item_post == Node.item_p && Node.next_post == Node.next_p && Node._lock_post == Node._lock_p && Stack._state_post == Stack._state_p && Stack.head_post == Stack.head_p && Stack._lock_post == Stack._lock_p && newValue_post == newValue && this_post == this && tid_post == tid;
assume $recorded.state_post == 1;                                                                   
 assert Y_Node._lock(tid, this, newValue , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
// Stack.head:                                                                                      
                                                                                                    
function {:inline} Y_Stack.head(tid : Tid, this: Stack, newValue: Node , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid): bool
{                                                                                                   
 ((isAccessible(Stack._state[this], tid) && leq(m#moverPath(ReadEval.Stack.head(tid: Tid,this: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)), _R)) ==> (Stack.head[this] == newValue))
                                                                                                    
}                                                                                                   
                                                                                                    
function {:inline} Invariant.Y_Stack.head(tid : Tid, this: Stack, newValue: Node , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid): bool
{                                                                                                   
 true                                                                                               
                                                                                                    
}                                                                                                   
                                                                                                    
procedure Y_Stack.head.Subsumes.W(tid : Tid, u : Tid, this: Stack, newValue: Node , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(tid);                                                                            
 requires ValidTid(u) && u != tid;                                                                  
                                                                                                    
{                                                                                                   
var Node.next_yield: [Node]Node;                                                                    
var Stack._lock_yield: [Stack]Tid;                                                                  
var Node.item_yield: [Node]int;                                                                     
var Node._state_yield: [Node]State;                                                                 
var tid_yield: Tid;                                                                                 
var this_yield: Stack;                                                                              
var $pc_yield: Phase;                                                                               
var u_yield: Tid;                                                                                   
var Stack.head_yield: [Stack]Node;                                                                  
var Node._lock_yield: [Node]Tid;                                                                    
var newValue_yield: Node;                                                                           
var Stack._state_yield: [Stack]State;                                                               
var $recorded.state_yield: int;                                                                     
                                                                                                    
 assume isAccessible(Stack._state[this], tid);                                                      
 assume isAccessible(Stack._state[this], u);                                                        
 assume !isError(m#moverPath(WriteEval.Stack.head(u: Tid,this: Stack,newValue: Node,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)));
                                                                                                    
assume Node._state_yield == Node._state && Node.item_yield == Node.item && Node.next_yield == Node.next && Node._lock_yield == Node._lock && Stack._state_yield == Stack._state && Stack.head_yield == Stack.head && Stack._lock_yield == Stack._lock && u_yield == u && newValue_yield == newValue && this_yield == this && tid_yield == tid;
assume $recorded.state_yield == 1;                                                                  
 assert Y_Stack.head(tid, this, newValue , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
                                                                                                    
procedure Y_Stack.head.Reflexive(tid : Tid, this: Stack , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(tid);                                                                            
                                                                                                    
{                                                                                                   
var Node.next_yield: [Node]Node;                                                                    
var Stack._lock_yield: [Stack]Tid;                                                                  
var Node.item_yield: [Node]int;                                                                     
var Node._state_yield: [Node]State;                                                                 
var tid_yield: Tid;                                                                                 
var this_yield: Stack;                                                                              
var $pc_yield: Phase;                                                                               
var Stack.head_yield: [Stack]Node;                                                                  
var Node._lock_yield: [Node]Tid;                                                                    
var Stack._state_yield: [Stack]State;                                                               
var $recorded.state_yield: int;                                                                     
                                                                                                    
 assume isAccessible(Stack._state[this], tid);                                                      
assume Node._state_yield == Node._state && Node.item_yield == Node.item && Node.next_yield == Node.next && Node._lock_yield == Node._lock && Stack._state_yield == Stack._state && Stack.head_yield == Stack.head && Stack._lock_yield == Stack._lock && this_yield == this && tid_yield == tid;
assume $recorded.state_yield == 1;                                                                  
 assert Y_Stack.head(tid, this, Stack.head[this] , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
                                                                                                    
procedure Y_Stack.head.Transitive(tid : Tid, this: Stack, newValue : Node , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid , Node._state_p: [Node]State, Node.item_p: [Node]int, Node.next_p: [Node]Node, Node._lock_p: [Node]Tid, Stack._state_p: [Stack]State, Stack.head_p: [Stack]Node, Stack._lock_p: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires StateInvariant(Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
 requires ValidTid(tid);                                                                            
                                                                                                    
{                                                                                                   
var newValue_pre: Node;                                                                             
var Node._lock_pre: [Node]Tid;                                                                      
var $recorded.state_pre: int;                                                                       
var Node._state_pre: [Node]State;                                                                   
var this_pre: Stack;                                                                                
var tid_pre: Tid;                                                                                   
var Stack._lock_pre: [Stack]Tid;                                                                    
var $pc_pre: Phase;                                                                                 
var Node.next_pre: [Node]Node;                                                                      
var Stack._state_pre: [Stack]State;                                                                 
var Stack.head_pre: [Stack]Node;                                                                    
var Node.item_pre: [Node]int;                                                                       
                                                                                                    
var Stack.head_post: [Stack]Node;                                                                   
var Stack._state_post: [Stack]State;                                                                
var $recorded.state_post: int;                                                                      
var newValue_post: Node;                                                                            
var this_post: Stack;                                                                               
var Node.item_post: [Node]int;                                                                      
var $pc_post: Phase;                                                                                
var Node._lock_post: [Node]Tid;                                                                     
var tid_post: Tid;                                                                                  
var Stack._lock_post: [Stack]Tid;                                                                   
var Node._state_post: [Node]State;                                                                  
var Node.next_post: [Node]Node;                                                                     
                                                                                                    
assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && newValue_pre == newValue && this_pre == this && tid_pre == tid;
assume $recorded.state_pre == 1;                                                                    
 assume isAccessible(Stack._state[this], tid);                                                      
 assume Y(tid , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock , Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
 assume Y_Stack.head(tid, this, newValue , Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
assume Node._state_post == Node._state_p && Node.item_post == Node.item_p && Node.next_post == Node.next_p && Node._lock_post == Node._lock_p && Stack._state_post == Stack._state_p && Stack.head_post == Stack.head_p && Stack._lock_post == Stack._lock_p && newValue_post == newValue && this_post == this && tid_post == tid;
assume $recorded.state_post == 1;                                                                   
 assert Y_Stack.head(tid, this, newValue , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
// Stack._lock:                                                                                     
                                                                                                    
function {:inline} Y_Stack._lock(tid : Tid, this: Stack, newValue: Tid , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid): bool
{                                                                                                   
 ((isAccessible(Stack._state[this], tid) && leq(m#moverPath(ReadEval.Stack._lock(tid: Tid,this: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)), _R)) ==> (Stack._lock[this] == newValue))
 &&(((Stack._lock[this]==tid)==(newValue==tid)))                                                    
                                                                                                    
}                                                                                                   
                                                                                                    
function {:inline} Invariant.Y_Stack._lock(tid : Tid, this: Stack, newValue: Tid , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid): bool
{                                                                                                   
 true                                                                                               
                                                                                                    
}                                                                                                   
                                                                                                    
procedure Y_Stack._lock.Subsumes.W(tid : Tid, u : Tid, this: Stack, newValue: Tid , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(tid);                                                                            
 requires ValidTid(u) && u != tid;                                                                  
                                                                                                    
{                                                                                                   
var Node.next_yield: [Node]Node;                                                                    
var Stack._lock_yield: [Stack]Tid;                                                                  
var Node.item_yield: [Node]int;                                                                     
var newValue_yield: Tid;                                                                            
var Node._state_yield: [Node]State;                                                                 
var tid_yield: Tid;                                                                                 
var this_yield: Stack;                                                                              
var $pc_yield: Phase;                                                                               
var u_yield: Tid;                                                                                   
var Stack.head_yield: [Stack]Node;                                                                  
var Node._lock_yield: [Node]Tid;                                                                    
var Stack._state_yield: [Stack]State;                                                               
var $recorded.state_yield: int;                                                                     
                                                                                                    
 assume isAccessible(Stack._state[this], tid);                                                      
 assume isAccessible(Stack._state[this], u);                                                        
 assume !isError(m#moverPath(WriteEval.Stack._lock(u: Tid,this: Stack,newValue: Tid,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)));
 assume leq(m#moverPath(ReadEval.Stack._lock(tid: Tid,this: Stack,Node._state,Node.item,Node.next,Node._lock,Stack._state,Stack.head,Stack._lock)), _N);
assume Node._state_yield == Node._state && Node.item_yield == Node.item && Node.next_yield == Node.next && Node._lock_yield == Node._lock && Stack._state_yield == Stack._state && Stack.head_yield == Stack.head && Stack._lock_yield == Stack._lock && u_yield == u && newValue_yield == newValue && this_yield == this && tid_yield == tid;
assume $recorded.state_yield == 1;                                                                  
 assert Y_Stack._lock(tid, this, newValue , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
                                                                                                    
procedure Y_Stack._lock.Reflexive(tid : Tid, this: Stack , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires ValidTid(tid);                                                                            
                                                                                                    
{                                                                                                   
var Node.next_yield: [Node]Node;                                                                    
var Stack._lock_yield: [Stack]Tid;                                                                  
var Node.item_yield: [Node]int;                                                                     
var Node._state_yield: [Node]State;                                                                 
var tid_yield: Tid;                                                                                 
var this_yield: Stack;                                                                              
var $pc_yield: Phase;                                                                               
var Stack.head_yield: [Stack]Node;                                                                  
var Node._lock_yield: [Node]Tid;                                                                    
var Stack._state_yield: [Stack]State;                                                               
var $recorded.state_yield: int;                                                                     
                                                                                                    
 assume isAccessible(Stack._state[this], tid);                                                      
assume Node._state_yield == Node._state && Node.item_yield == Node.item && Node.next_yield == Node.next && Node._lock_yield == Node._lock && Stack._state_yield == Stack._state && Stack.head_yield == Stack.head && Stack._lock_yield == Stack._lock && this_yield == this && tid_yield == tid;
assume $recorded.state_yield == 1;                                                                  
 assert Y_Stack._lock(tid, this, Stack._lock[this] , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
                                                                                                    
procedure Y_Stack._lock.Transitive(tid : Tid, this: Stack, newValue : Tid , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid , Node._state_p: [Node]State, Node.item_p: [Node]int, Node.next_p: [Node]Node, Node._lock_p: [Node]Tid, Stack._state_p: [Stack]State, Stack.head_p: [Stack]Node, Stack._lock_p: [Stack]Tid)
 requires StateInvariant(Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
 requires StateInvariant(Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
 requires ValidTid(tid);                                                                            
                                                                                                    
{                                                                                                   
var Node._lock_pre: [Node]Tid;                                                                      
var $recorded.state_pre: int;                                                                       
var Node._state_pre: [Node]State;                                                                   
var this_pre: Stack;                                                                                
var tid_pre: Tid;                                                                                   
var Stack._lock_pre: [Stack]Tid;                                                                    
var $pc_pre: Phase;                                                                                 
var Node.next_pre: [Node]Node;                                                                      
var Stack._state_pre: [Stack]State;                                                                 
var Stack.head_pre: [Stack]Node;                                                                    
var newValue_pre: Tid;                                                                              
var Node.item_pre: [Node]int;                                                                       
                                                                                                    
var Stack.head_post: [Stack]Node;                                                                   
var Stack._state_post: [Stack]State;                                                                
var $recorded.state_post: int;                                                                      
var this_post: Stack;                                                                               
var Node.item_post: [Node]int;                                                                      
var $pc_post: Phase;                                                                                
var Node._lock_post: [Node]Tid;                                                                     
var tid_post: Tid;                                                                                  
var Stack._lock_post: [Stack]Tid;                                                                   
var Node._state_post: [Node]State;                                                                  
var Node.next_post: [Node]Node;                                                                     
var newValue_post: Tid;                                                                             
                                                                                                    
assume Node._state_pre == Node._state && Node.item_pre == Node.item && Node.next_pre == Node.next && Node._lock_pre == Node._lock && Stack._state_pre == Stack._state && Stack.head_pre == Stack.head && Stack._lock_pre == Stack._lock && newValue_pre == newValue && this_pre == this && tid_pre == tid;
assume $recorded.state_pre == 1;                                                                    
 assume isAccessible(Stack._state[this], tid);                                                      
 assume Y(tid , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock , Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
 assume Y_Stack._lock(tid, this, newValue , Node._state_p, Node.item_p, Node.next_p, Node._lock_p, Stack._state_p, Stack.head_p, Stack._lock_p);
assume Node._state_post == Node._state_p && Node.item_post == Node.item_p && Node.next_post == Node.next_p && Node._lock_post == Node._lock_p && Stack._state_post == Stack._state_p && Stack.head_post == Stack.head_p && Stack._lock_post == Stack._lock_p && newValue_post == newValue && this_post == this && tid_post == tid;
assume $recorded.state_post == 1;                                                                   
 assert Y_Stack._lock(tid, this, newValue , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock);
}                                                                                                   
                                                                                                    
                                                                                                    
function {:inline} Y(tid : Tid , Node._state: [Node]State, Node.item: [Node]int, Node.next: [Node]Node, Node._lock: [Node]Tid, Stack._state: [Stack]State, Stack.head: [Stack]Node, Stack._lock: [Stack]Tid , Node._state_p: [Node]State, Node.item_p: [Node]int, Node.next_p: [Node]Node, Node._lock_p: [Node]Tid, Stack._state_p: [Stack]State, Stack.head_p: [Stack]Node, Stack._lock_p: [Stack]Tid): bool
{                                                                                                   
 (forall this: Node :: Y_Node.item(tid : Tid, this, Node.item_p[this] , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock))
 && (forall this: Node :: Y_Node.next(tid : Tid, this, Node.next_p[this] , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock))
 && (forall this: Node :: Y_Node._lock(tid : Tid, this, Node._lock_p[this] , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock))
 && (forall this: Stack :: Y_Stack.head(tid : Tid, this, Stack.head_p[this] , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock))
 && (forall this: Stack :: Y_Stack._lock(tid : Tid, this, Stack._lock_p[this] , Node._state, Node.item, Node.next, Node._lock, Stack._state, Stack.head, Stack._lock))
 && (forall _i : Node :: isShared(Node._state[_i]) ==> isShared(Node._state_p[_i]))                 
 && (forall _i : Node :: isLocal(Node._state[_i], tid) <==> isLocal(Node._state_p[_i], tid))        
 && (forall _i : Stack :: isShared(Stack._state[_i]) ==> isShared(Stack._state_p[_i]))              
 && (forall _i : Stack :: isLocal(Stack._state[_i], tid) <==> isLocal(Stack._state_p[_i], tid))     
                                                                                                    
}                                                                                                   
                                                                                                    
                                                                                                    
// 951.1-1307.2: (Method:15.3)
// 991.1-991.24: (15.3): Bad tid
// 992.1-992.39: (15.3): this is not global
// 1146.1-1146.29: (19.5): Cannot have potential null deference in left-mover part.
// 1150.1-1150.27: (19.5): Reduction failure
// 1152.2-1154.2: (class anchor.sink.VarDeclStmt:20.5)
// 1155.2-1164.39: (class anchor.sink.Alloc:20.5)
// 1165.2-1167.2: (class anchor.sink.VarDeclStmt:20.5)
// 1168.2-1185.27: (class anchor.sink.Read:20.5)
// 1180.1-1180.29: (20.5): Cannot have potential null deference in left-mover part.
// 1184.1-1184.27: (20.5): Reduction failure
// 1188.2-1190.2: (class anchor.sink.VarDeclStmt:20.5)
// 1191.2-1193.2: (class anchor.sink.VarDeclStmt:20.5)
// 1194.2-1196.2: (class anchor.sink.VarDeclStmt:20.5)
// 1197.2-1200.17: (class anchor.sink.Assign:20.5)
// 1201.2-1204.17: (class anchor.sink.Assign:20.5)
// 1205.2-1208.17: (class anchor.sink.Assign:20.5)
// 1209.2-1212.32: (class anchor.sink.Assume:5.3)
// 1213.2-1216.40: (class anchor.sink.Assume:5.3)
// 1218.2-1234.30: (class anchor.sink.Write:6.5)
// 1230.1-1230.30: (6.5): Cannot have potential null deference in left-mover part.
// 1233.1-1233.27: (6.5): Reduction failure
// 1236.2-1257.2: (class anchor.sink.Write:7.5)
// 1248.1-1248.30: (7.5): Cannot have potential null deference in left-mover part.
// 1251.1-1251.27: (7.5): Reduction failure
// 1255.1-1255.61: (7.5): next$1 became shared, but next$1.next may not be shared.
// 1258.2-1261.21: (class anchor.sink.Break:5.29)
// 1264.2-1285.2: (class anchor.sink.Write:21.5)
// 1276.1-1276.29: (21.5): Cannot have potential null deference in left-mover part.
// 1279.1-1279.27: (21.5): Reduction failure
// 1283.1-1283.59: (21.5): node became shared, but node.next may not be shared.
// 1289.1-1289.29: (22.5): Cannot have potential null deference in left-mover part.
// 1291.1-1291.34: (22.5): lock not held
// 1293.1-1293.27: (22.5): Reduction failure
// 1295.2-1306.9: (class anchor.sink.Return:18.30)
// 1305.1-1305.21: (18.30): Method returns before completing actions in spec
// 1308.1-1928.2: (Method:25.3)
// 1350.1-1350.24: (25.3): Bad tid
// 1351.1-1351.39: (25.3): this is not global
// 1661.1-1661.29: (30.5): Cannot have potential null deference in left-mover part.
// 1665.1-1665.27: (30.5): Reduction failure
// 1669.2-1684.14: (class anchor.sink.While:31.5)
// 1683.1-1683.36: (31.5): Cannot construct possible Spec States for loop head.
// 1686.1-1686.27: (25.3): Bad tid
// 1687.1-1687.42: (25.3): this is not global
// 1689.114-1690.81: (31.5): invariant holds(this, tid) may not hold
// 1691.1-1691.211: (31.5): Loop does not preserve yields_as annotation for field item
// 1692.1-1692.211: (31.5): Loop does not preserve yields_as annotation for field next
// 1693.1-1693.214: (31.5): Loop does not preserve yields_as annotation for field head
// 1694.1-1694.31: (31.5): Phase must be invariant at loop head
// 1695.1-1695.30: (31.5): Potentially infinite loop cannot be in post-commit phase.
// 1706.3-1708.3: (class anchor.sink.VarDeclStmt:31.22)
// 1709.3-1711.3: (class anchor.sink.VarDeclStmt:31.12)
// 1712.3-1729.28: (class anchor.sink.Read:31.12)
// 1724.1-1724.30: (31.12): Cannot have potential null deference in left-mover part.
// 1728.1-1728.28: (31.12): Reduction failure
// 1730.3-1733.29: (class anchor.sink.Assign:31.22)
// 1735.4-1738.10: (class anchor.sink.Break:31.5)
// 1744.1-1744.30: (34.7): Cannot have potential null deference in left-mover part.
// 1746.1-1746.35: (34.7): lock not held
// 1748.1-1748.28: (34.7): Reduction failure
// 1750.3-1764.37: (class anchor.sink.Yield:35.7)
// 1764.1-1764.37: (35.7): Atomic block is not pure and does not conform to spec
// 1768.1-1768.30: (36.7): Cannot have potential null deference in left-mover part.
// 1772.1-1772.28: (36.7): Reduction failure
// 1776.1-1776.28: (31.5): Phase must be invariant at loop head
// 1786.2-1788.2: (class anchor.sink.VarDeclStmt:38.5)
// 1789.2-1791.2: (class anchor.sink.VarDeclStmt:38.5)
// 1792.2-1809.27: (class anchor.sink.Read:38.5)
// 1804.1-1804.29: (38.5): Cannot have potential null deference in left-mover part.
// 1808.1-1808.27: (38.5): Reduction failure
// 1810.2-1827.27: (class anchor.sink.Read:38.5)
// 1822.1-1822.28: (38.5): Cannot have potential null deference in left-mover part.
// 1826.1-1826.27: (38.5): Reduction failure
// 1828.2-1830.2: (class anchor.sink.VarDeclStmt:39.5)
// 1831.2-1833.2: (class anchor.sink.VarDeclStmt:39.5)
// 1834.2-1851.27: (class anchor.sink.Read:39.5)
// 1846.1-1846.29: (39.5): Cannot have potential null deference in left-mover part.
// 1850.1-1850.27: (39.5): Reduction failure
// 1852.2-1869.26: (class anchor.sink.Read:39.5)
// 1864.1-1864.28: (39.5): Cannot have potential null deference in left-mover part.
// 1868.1-1868.27: (39.5): Reduction failure
// 1871.2-1892.2: (class anchor.sink.Write:39.5)
// 1883.1-1883.29: (39.5): Cannot have potential null deference in left-mover part.
// 1886.1-1886.27: (39.5): Reduction failure
// 1890.1-1890.59: (39.5): tmp5 became shared, but tmp5.next may not be shared.
// 1896.1-1896.29: (40.5): Cannot have potential null deference in left-mover part.
// 1898.1-1898.34: (40.5): lock not held
// 1900.1-1900.27: (40.5): Reduction failure
// 1902.2-1914.9: (class anchor.sink.Return:41.5)
// 1913.1-1913.21: (41.5): Method returns before completing actions in spec
// 1915.2-1927.9: (class anchor.sink.Return:29.20)
// 1926.1-1926.21: (29.20): Method returns before completing actions in spec
// 2015.1-2015.34: (2.3): Node.item failed Write-Write Right-Mover Check
// 2080.1-2080.30: (2.3): Node.item failed Write-Read Right-Mover Check
// 2149.1-2149.34: (2.3): Node.item failed Write-Write Left-Mover Check
// 2215.1-2215.30: (2.3): Node.item failed Write-Read Left-Mover Check
// 2278.1-2278.34: (2.3): Node.item failed Read-Write Right-Mover Check
// 2344.1-2344.34: (2.3): Node.item failed Read-Write Left-Mover Check
// 2409.1-2409.34: (3.3): Node.next failed Write-Write Right-Mover Check
// 2474.1-2474.30: (3.3): Node.next failed Write-Read Right-Mover Check
// 2543.1-2543.34: (3.3): Node.next failed Write-Write Left-Mover Check
// 2609.1-2609.30: (3.3): Node.next failed Write-Read Left-Mover Check
// 2672.1-2672.34: (3.3): Node.next failed Read-Write Right-Mover Check
// 2738.1-2738.34: (3.3): Node.next failed Read-Write Left-Mover Check
// 2803.1-2803.34: (13.3): Stack.head failed Write-Write Right-Mover Check
// 2868.1-2868.30: (13.3): Stack.head failed Write-Read Right-Mover Check
// 2937.1-2937.34: (13.3): Stack.head failed Write-Write Left-Mover Check
// 3003.1-3003.30: (13.3): Stack.head failed Write-Read Left-Mover Check
// 3066.1-3066.34: (13.3): Stack.head failed Read-Write Right-Mover Check
// 3132.1-3132.34: (13.3): Stack.head failed Read-Write Left-Mover Check
// 3209.1-3209.140: (2.3): Node.item is not Write-Write Stable with respect to Node.item (case A.1)
// 3210.1-3210.101: (2.3): Node.item is not Write-Write Stable with respect to Node.item (case A.2)
// 3211.1-3211.158: (2.3): Node.item is not Write-Write Stable with respect to Node.item (case A.3)
// 3316.1-3316.140: (2.3): Node.item is not Write-Write Stable with respect to Node.item (case C)
// 3426.1-3426.144: (2.3): Node.item is not Write-Write Stable with respect to Node.item (case D)
// 3427.1-3427.144: (2.3): Node.item is not Write-Write Stable with respect to Node.item (case R)
// 3504.1-3504.136: (2.3): Node.item is not Read-Write Stable with respect to Node.item (case F)
// 3505.1-3505.136: (2.3): Node.item is not Read-Write Stable with respect to Node.item (case H)
// 3506.1-3506.146: (2.3): Node.item is not Read-Write Stable with respect to Node.item (case I)
// 3582.1-3582.136: (2.3): Node.item is not Write-Read Stable with respect to Node.item (case J)
// 3583.1-3583.136: (2.3): Node.item is not Write-Read Stable with respect to Node.item (case K)
// 3584.1-3584.99: (2.3): Node.item is not Write-Read Stable with respect to Node.item (case L)
// 3662.1-3662.140: (3.3): Node.next is not Write-Write Stable with respect to Node.item (case A.1)
// 3663.1-3663.101: (3.3): Node.next is not Write-Write Stable with respect to Node.item (case A.2)
// 3664.1-3664.158: (3.3): Node.next is not Write-Write Stable with respect to Node.item (case A.3)
// 3769.1-3769.140: (2.3): Node.item is not Write-Write Stable with respect to Node.next (case C)
// 3879.1-3879.144: (2.3): Node.item is not Write-Write Stable with respect to Node.next (case D)
// 3880.1-3880.144: (2.3): Node.item is not Write-Write Stable with respect to Node.next (case R)
// 3957.1-3957.136: (2.3): Node.item is not Read-Write Stable with respect to Node.next (case F)
// 3958.1-3958.136: (2.3): Node.item is not Read-Write Stable with respect to Node.next (case H)
// 3959.1-3959.146: (2.3): Node.item is not Read-Write Stable with respect to Node.next (case I)
// 4035.1-4035.136: (3.3): Node.next is not Write-Read Stable with respect to Node.item (case J)
// 4036.1-4036.136: (3.3): Node.next is not Write-Read Stable with respect to Node.item (case K)
// 4037.1-4037.99: (3.3): Node.next is not Write-Read Stable with respect to Node.item (case L)
// 4115.1-4115.140: (13.3): Stack.head is not Write-Write Stable with respect to Node.item (case A.1)
// 4116.1-4116.101: (13.3): Stack.head is not Write-Write Stable with respect to Node.item (case A.2)
// 4117.1-4117.156: (13.3): Stack.head is not Write-Write Stable with respect to Node.item (case A.3)
// 4222.1-4222.140: (2.3): Node.item is not Write-Write Stable with respect to Stack.head (case C)
// 4332.1-4332.144: (2.3): Node.item is not Write-Write Stable with respect to Stack.head (case D)
// 4333.1-4333.144: (2.3): Node.item is not Write-Write Stable with respect to Stack.head (case R)
// 4410.1-4410.136: (2.3): Node.item is not Read-Write Stable with respect to Stack.head (case F)
// 4411.1-4411.136: (2.3): Node.item is not Read-Write Stable with respect to Stack.head (case H)
// 4412.1-4412.144: (2.3): Node.item is not Read-Write Stable with respect to Stack.head (case I)
// 4488.1-4488.136: (13.3): Stack.head is not Write-Read Stable with respect to Node.item (case J)
// 4489.1-4489.136: (13.3): Stack.head is not Write-Read Stable with respect to Node.item (case K)
// 4490.1-4490.99: (13.3): Stack.head is not Write-Read Stable with respect to Node.item (case L)
// 4568.1-4568.140: (2.3): Node.item is not Write-Write Stable with respect to Node.next (case A.1)
// 4569.1-4569.101: (2.3): Node.item is not Write-Write Stable with respect to Node.next (case A.2)
// 4570.1-4570.158: (2.3): Node.item is not Write-Write Stable with respect to Node.next (case A.3)
// 4675.1-4675.140: (3.3): Node.next is not Write-Write Stable with respect to Node.item (case C)
// 4785.1-4785.144: (3.3): Node.next is not Write-Write Stable with respect to Node.item (case D)
// 4786.1-4786.144: (3.3): Node.next is not Write-Write Stable with respect to Node.item (case R)
// 4863.1-4863.136: (3.3): Node.next is not Read-Write Stable with respect to Node.item (case F)
// 4864.1-4864.136: (3.3): Node.next is not Read-Write Stable with respect to Node.item (case H)
// 4865.1-4865.146: (3.3): Node.next is not Read-Write Stable with respect to Node.item (case I)
// 4941.1-4941.136: (2.3): Node.item is not Write-Read Stable with respect to Node.next (case J)
// 4942.1-4942.136: (2.3): Node.item is not Write-Read Stable with respect to Node.next (case K)
// 4943.1-4943.99: (2.3): Node.item is not Write-Read Stable with respect to Node.next (case L)
// 5021.1-5021.140: (3.3): Node.next is not Write-Write Stable with respect to Node.next (case A.1)
// 5022.1-5022.101: (3.3): Node.next is not Write-Write Stable with respect to Node.next (case A.2)
// 5023.1-5023.158: (3.3): Node.next is not Write-Write Stable with respect to Node.next (case A.3)
// 5128.1-5128.140: (3.3): Node.next is not Write-Write Stable with respect to Node.next (case C)
// 5238.1-5238.144: (3.3): Node.next is not Write-Write Stable with respect to Node.next (case D)
// 5239.1-5239.144: (3.3): Node.next is not Write-Write Stable with respect to Node.next (case R)
// 5316.1-5316.136: (3.3): Node.next is not Read-Write Stable with respect to Node.next (case F)
// 5317.1-5317.136: (3.3): Node.next is not Read-Write Stable with respect to Node.next (case H)
// 5318.1-5318.146: (3.3): Node.next is not Read-Write Stable with respect to Node.next (case I)
// 5394.1-5394.136: (3.3): Node.next is not Write-Read Stable with respect to Node.next (case J)
// 5395.1-5395.136: (3.3): Node.next is not Write-Read Stable with respect to Node.next (case K)
// 5396.1-5396.99: (3.3): Node.next is not Write-Read Stable with respect to Node.next (case L)
// 5474.1-5474.140: (13.3): Stack.head is not Write-Write Stable with respect to Node.next (case A.1)
// 5475.1-5475.101: (13.3): Stack.head is not Write-Write Stable with respect to Node.next (case A.2)
// 5476.1-5476.156: (13.3): Stack.head is not Write-Write Stable with respect to Node.next (case A.3)
// 5581.1-5581.140: (3.3): Node.next is not Write-Write Stable with respect to Stack.head (case C)
// 5691.1-5691.144: (3.3): Node.next is not Write-Write Stable with respect to Stack.head (case D)
// 5692.1-5692.144: (3.3): Node.next is not Write-Write Stable with respect to Stack.head (case R)
// 5769.1-5769.136: (3.3): Node.next is not Read-Write Stable with respect to Stack.head (case F)
// 5770.1-5770.136: (3.3): Node.next is not Read-Write Stable with respect to Stack.head (case H)
// 5771.1-5771.144: (3.3): Node.next is not Read-Write Stable with respect to Stack.head (case I)
// 5847.1-5847.136: (13.3): Stack.head is not Write-Read Stable with respect to Node.next (case J)
// 5848.1-5848.136: (13.3): Stack.head is not Write-Read Stable with respect to Node.next (case K)
// 5849.1-5849.99: (13.3): Stack.head is not Write-Read Stable with respect to Node.next (case L)
// 5927.1-5927.140: (2.3): Node.item is not Write-Write Stable with respect to Stack.head (case A.1)
// 5928.1-5928.101: (2.3): Node.item is not Write-Write Stable with respect to Stack.head (case A.2)
// 5929.1-5929.156: (2.3): Node.item is not Write-Write Stable with respect to Stack.head (case A.3)
// 6034.1-6034.140: (13.3): Stack.head is not Write-Write Stable with respect to Node.item (case C)
// 6144.1-6144.144: (13.3): Stack.head is not Write-Write Stable with respect to Node.item (case D)
// 6145.1-6145.144: (13.3): Stack.head is not Write-Write Stable with respect to Node.item (case R)
// 6222.1-6222.136: (13.3): Stack.head is not Read-Write Stable with respect to Node.item (case F)
// 6223.1-6223.136: (13.3): Stack.head is not Read-Write Stable with respect to Node.item (case H)
// 6224.1-6224.144: (13.3): Stack.head is not Read-Write Stable with respect to Node.item (case I)
// 6300.1-6300.136: (2.3): Node.item is not Write-Read Stable with respect to Stack.head (case J)
// 6301.1-6301.136: (2.3): Node.item is not Write-Read Stable with respect to Stack.head (case K)
// 6302.1-6302.99: (2.3): Node.item is not Write-Read Stable with respect to Stack.head (case L)
// 6380.1-6380.140: (3.3): Node.next is not Write-Write Stable with respect to Stack.head (case A.1)
// 6381.1-6381.101: (3.3): Node.next is not Write-Write Stable with respect to Stack.head (case A.2)
// 6382.1-6382.156: (3.3): Node.next is not Write-Write Stable with respect to Stack.head (case A.3)
// 6487.1-6487.140: (13.3): Stack.head is not Write-Write Stable with respect to Node.next (case C)
// 6597.1-6597.144: (13.3): Stack.head is not Write-Write Stable with respect to Node.next (case D)
// 6598.1-6598.144: (13.3): Stack.head is not Write-Write Stable with respect to Node.next (case R)
// 6675.1-6675.136: (13.3): Stack.head is not Read-Write Stable with respect to Node.next (case F)
// 6676.1-6676.136: (13.3): Stack.head is not Read-Write Stable with respect to Node.next (case H)
// 6677.1-6677.144: (13.3): Stack.head is not Read-Write Stable with respect to Node.next (case I)
// 6753.1-6753.136: (3.3): Node.next is not Write-Read Stable with respect to Stack.head (case J)
// 6754.1-6754.136: (3.3): Node.next is not Write-Read Stable with respect to Stack.head (case K)
// 6755.1-6755.99: (3.3): Node.next is not Write-Read Stable with respect to Stack.head (case L)
// 6833.1-6833.140: (13.3): Stack.head is not Write-Write Stable with respect to Stack.head (case A.1)
// 6834.1-6834.101: (13.3): Stack.head is not Write-Write Stable with respect to Stack.head (case A.2)
// 6835.1-6835.158: (13.3): Stack.head is not Write-Write Stable with respect to Stack.head (case A.3)
// 6940.1-6940.140: (13.3): Stack.head is not Write-Write Stable with respect to Stack.head (case C)
// 7050.1-7050.144: (13.3): Stack.head is not Write-Write Stable with respect to Stack.head (case D)
// 7051.1-7051.144: (13.3): Stack.head is not Write-Write Stable with respect to Stack.head (case R)
// 7128.1-7128.136: (13.3): Stack.head is not Read-Write Stable with respect to Stack.head (case F)
// 7129.1-7129.136: (13.3): Stack.head is not Read-Write Stable with respect to Stack.head (case H)
// 7130.1-7130.146: (13.3): Stack.head is not Read-Write Stable with respect to Stack.head (case I)
// 7206.1-7206.136: (13.3): Stack.head is not Write-Read Stable with respect to Stack.head (case J)
// 7207.1-7207.136: (13.3): Stack.head is not Write-Read Stable with respect to Stack.head (case K)
// 7208.1-7208.99: (13.3): Stack.head is not Write-Read Stable with respect to Stack.head (case L)
// 7243.1-7266.2: (2.3): yields_as clause for Node.item is not valid
// 7271.1-7289.2: (2.3): yields_as clause for Node.item is not reflexive
// 7295.1-7331.2: (2.3): yields_as clause for Node.item is not transitive
// 7350.1-7373.2: (3.3): yields_as clause for Node.next is not valid
// 7378.1-7396.2: (3.3): yields_as clause for Node.next is not reflexive
// 7402.1-7438.2: (3.3): yields_as clause for Node.next is not transitive
// 7458.1-7481.2: (7.32): yields_as clause for Node._lock is not valid
// 7486.1-7504.2: (7.32): yields_as clause for Node._lock is not reflexive
// 7510.1-7546.2: (7.32): yields_as clause for Node._lock is not transitive
// 7565.1-7588.2: (13.3): yields_as clause for Stack.head is not valid
// 7593.1-7611.2: (13.3): yields_as clause for Stack.head is not reflexive
// 7617.1-7653.2: (13.3): yields_as clause for Stack.head is not transitive
// 7673.1-7696.2: (7.32): yields_as clause for Stack._lock is not valid
// 7701.1-7719.2: (7.32): yields_as clause for Stack._lock is not reflexive
// 7725.1-7761.2: (7.32): yields_as clause for Stack._lock is not transitive
