let emp_bytes = Bytes.empty

let check_overflow x y = x + y < x


module BMap = Map.Make(Bytes)
module IMap = Map.Make(Int)
module I6Map = Map.Make(Int64)

module RWMutex: sig
  type t
  val create : unit -> t

  val r_lock : t -> unit
  val r_unlock : t -> unit

  val w_lock : t -> unit
  val w_unlock : t -> unit

  val with_r_lock : t -> (unit -> 'a) -> 'a
  val with_w_lock : t -> (unit -> 'a) -> 'a
end = struct 

  type t = {
    lock : Mutex.t;              (* Protects all shared fields *)
    can_read : Condition.t;      (* Readers wait here *)
    can_write : Condition.t;     (* Writers wait here *)
    mutable readers : int;       (* Number of active readers *)
    mutable writers : int;       (* Number of active writers (0 or 1) *)
    mutable waiting_writers : int; (* Writers waiting — gives them priority *)
  }

  let create () =
    {
      lock = Mutex.create ();
      can_read = Condition.create ();
      can_write = Condition.create ();
      readers = 0;
      writers = 0;
      waiting_writers = 0;
    }

  let r_lock t =
    Mutex.lock t.lock;
    (* Block readers if a writer is active OR any writers are waiting *)
    while t.writers > 0 || t.waiting_writers > 0 do
      Condition.wait t.can_read t.lock
    done;
    t.readers <- t.readers + 1;
    Mutex.unlock t.lock

  let r_unlock t =
    Mutex.lock t.lock;
    t.readers <- t.readers - 1;
    (* If no more readers, a writer may proceed *)
    if t.readers = 0 then
      Condition.signal t.can_write;
    Mutex.unlock t.lock

  let w_lock t =
    Mutex.lock t.lock;
    t.waiting_writers <- t.waiting_writers + 1;
    (* Writers wait until no active readers or writers *)
    while t.readers > 0 || t.writers > 0 do
      Condition.wait t.can_write t.lock
    done;
    t.waiting_writers <- t.waiting_writers - 1;
    t.writers <- 1;
    Mutex.unlock t.lock

  let w_unlock t =
    Mutex.lock t.lock;
    t.writers <- 0;

    (* Prefer writers over readers *)
    if t.waiting_writers > 0 then
      Condition.signal t.can_write
    else
      Condition.broadcast t.can_read;

    Mutex.unlock t.lock

  let with_r_lock t f =
    r_lock t;
    let finally () = r_unlock t in
    Fun.protect ~finally f

  let with_w_lock t f =
    w_lock t;
    let finally () = w_unlock t in
    Fun.protect ~finally f
    
end

module Wait_group : sig
  type t

  val create : unit -> t
  val add : t -> int -> unit
  val done_ : t -> unit
  val wait : t -> unit
end = struct
  type t = {
    mutable count : int;
    mutex : Mutex.t;
    cond : Condition.t;
  }

  let create () =
    { count = 0; mutex = Mutex.create (); cond = Condition.create () }

  let add t n =
    Mutex.lock t.mutex;
    t.count <- t.count + n;
    (* No need to signal; waiters only wake on reaching zero. *)
    Mutex.unlock t.mutex

  let done_ t =
    Mutex.lock t.mutex;
    t.count <- t.count - 1;
    if t.count = 0 then
      Condition.broadcast t.cond;
    Mutex.unlock t.mutex

  let wait t =
    Mutex.lock t.mutex;
    (* Wait until count reaches zero *)
    while t.count > 0 do
      Condition.wait t.cond t.mutex
    done;
    Mutex.unlock t.mutex
end
