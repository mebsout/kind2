(** Simple imperative union-find data structure *)

type 'a t = { mutable rank : int; mutable parent : 'a t; data : 'a }

let make x =
  let rec c = { rank = 0; parent = c; data = x } in
  c

let rec find i =
  let p = i.parent in
  if p == i then
    i
  else begin
    let r = find p in
    i.parent <- r;
    r
  end

let union i j =
  let ri = find i in
  let rj = find j in
  if ri != rj then begin
    if ri.rank < rj.rank then
      ri.parent <- rj
    else begin
      rj.parent <- ri;
      if ri.rank = rj.rank then
        ri.rank <- ri.rank + 1
    end
  end

let data x = x.data

let equal = (==)
