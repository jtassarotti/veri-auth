open Auth

module type TRIMERKLE =
  functor (K : AUTHENTIKIT) -> sig
    open K
       
    type path
    val path_empty : path
    val path_left : path -> path
    val path_middle : path -> path
    val path_right : path -> path

    type tree = [`left of string | `right of string * (tree auth * (tree auth * tree auth)) ]
    type tree_auth = tree auth

    val make_leaf : string -> tree_auth
    val make_branch : string -> tree_auth -> tree_auth -> tree_auth -> tree_auth
    val init_tree : int -> tree_auth
    val retrieve :
      path -> tree_auth -> string option authenticated_computation
    val update :
      path -> string -> tree_auth -> tree_auth option authenticated_computation
    val from_list : string list -> tree_auth
    val retrieve_list : path list -> tree_auth -> (string option list) authenticated_computation
    val compare : tree_auth -> tree_auth -> bool authenticated_computation
    val contains : string -> tree_auth -> bool authenticated_computation
  end


module TriMerkle : TRIMERKLE =
  functor (K : AUTHENTIKIT) -> struct
    open K

    type path = [`L|`M|`R] list
    let path_empty = []
    let path_left path = `L :: path
    let path_middle path = `M :: path
    let path_right path = `R :: path

    type tree = [`left of string | `right of string * (tree auth * (tree auth * tree auth)) ]
    type tree_auth = tree auth
    let tree : [`left of string |`right of string * (tree auth * (tree auth * tree auth))] Authenticatable.evidence =
      Authenticatable.(sum string (pair string (pair auth (pair auth auth))))

    let make_leaf s =
      auth tree (`left s)

    let make_branch s l m r =
      auth tree (`right (s, (l, (m, r))))

    let null_leaf = make_leaf ""

    let rec init_tree depth =
      if depth = 0 then null_leaf
      else make_branch "" (init_tree (depth-1)) (init_tree (depth-1)) (init_tree (depth-1))

    let rec retrieve path t =
      bind (unauth tree t)
        (fun t ->
          match path, t with
          | [], `left s -> return (Some s)
          | [], `right (s, _) -> return (Some s)
          | `L::path, `right (s, (l, (m, r))) -> retrieve path l
          | `M::path, `right (s, (l, (m, r))) -> retrieve path m
          | `R::path, `right (s, (l, (m, r))) -> retrieve path r
          | _, _ -> return None)

    let rec update path v t =
      bind (unauth tree t)
        (fun t ->
          match path, t with
          | [], `left _ ->
            return (Some (make_leaf v))
          | [], `right (_, (l, (m, r))) ->
            return (Some (make_branch v l m r))
          | `L::path, `right (s, (l, (m, r))) ->
            bind (update path v l)
              (function | None -> return None | Some l' -> return (Some (make_branch s l' m r)))
          | `M::path, `right (s, (l, (m, r))) ->
            bind (update path v m)
              (function | None -> return None | Some m' -> return (Some (make_branch s l m' r)))
          | `R::path, `right (s, (l, (m, r))) ->
            bind (update path v r)
              (function | None -> return None | Some r' -> return (Some (make_branch s l m r')))
          | _ -> return None)

    (* Not in Atkey; based on the version from lambda-auth *)

    let tri_split l =
      let l1 = List.filteri (fun i a -> i mod 3 = 0) l in
      let l2 = List.filteri (fun i a -> i mod 3 = 1) l in
      let l3 = List.filteri (fun i a -> i mod 3 = 2) l in
      l1, l2, l3
      
    let rec from_list x =
      match x with
      | [] -> failwith "empty"
      | [a] -> make_leaf a
      | s::l -> let left, middle, right = tri_split l in
        make_branch s (from_list left) (from_list middle) (from_list right)

    (* Not in either source *)

    let rec retrieve_list paths t =
      match paths with
      | [] -> return []
      | p :: paths ->
         bind (retrieve p t)
           (fun v ->
             bind (retrieve_list paths t)
               (fun vs ->
                return (v :: vs)))

    let rec compare t1 t2 =
      bind (unauth tree t1)
        (fun t1 ->
          bind (unauth tree t2)
            (fun t2 ->
              match t1, t2 with
              | `left s1, `left s2 -> return (String.equal s1 s2)
              | `right (s1, (l1, (m1, r1))), `right (s2, (l2, (m2, r2))) ->
                if String.equal s1 s2 then
                  bind (compare l1 l2)
                    (fun b1 -> 
                      if b1
                        then 
                          bind (compare m1 m2)
                          (fun b2 ->
                            if b2
                              then compare r1 r2
                              else  return b2)
                          else return b1
                      )
                else return false
              | _ -> return false
              )
          )

    let rec contains s t =
      bind (unauth tree t) (
        function
          `left s' -> return (String.equal s s')
        | `right (s', (l, (m, r))) ->
          if String.equal s s' then return true
          else
            bind (contains s l) (
              function
                true -> return true
              | false ->
                bind (contains s m) (
                  function
                    true -> return true
                  | false -> contains s r
                )
            )
        )
  end
