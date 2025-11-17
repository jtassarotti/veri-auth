open Lwt.Infix
open Lwt.Syntax

type wq_req = {
  uid: int;
  pk: bytes;
  ver: int
}

type wq_resp = {
  err: bool
}

type work = {
  mu: Mutex.t;
  cond: Condition.t;
  don: bool ref;
  req: wq_req;
  mutable resp: wq_resp
}

type workq = {
  mu: Mutex.t;
  cond: Condition.t;
  work: work Queue.t
}

let err_resp = { err = true }
let ok_resp = { err = false }

let new_work (req: wq_req): work =
  { mu = Mutex.create ();
    cond = Condition.create ();
    don = ref false;
    req = req;
    resp = ok_resp }

let finish (w : work) =
  Mutex.lock w.mu;
  w.don := true;
  Condition.signal w.cond;
  Mutex.unlock w.mu

let do_q (wq: workq) (req: wq_req): wq_resp =
  let w = new_work req in
  Mutex.lock wq.mu;
  Queue.add w wq.work;
  Condition.signal w.cond;
  Mutex.unlock w.mu;

  Mutex.lock w.mu;
  let rec aux () =
    if !(w.don) then ()
    else
      Condition.wait w.cond w.mu; aux ()
  in
  aux ();
  Mutex.unlock w.mu;
  w.resp

let get (wq: workq): work Queue.t =
  Mutex.lock wq.mu;
  let rec aux () =
    if Queue.is_empty wq.work then ()
    else
      Condition.wait wq.cond wq.mu; aux ()
  in
  aux ();

  let work = Queue.copy wq.work in
  Queue.clear wq.work;
  Mutex.unlock wq.mu;
  work

let new_workq (): workq =
  { mu = Mutex.create ();
    cond = Condition.create ();
    work = Queue.create () }

