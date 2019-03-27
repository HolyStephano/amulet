(* Implicit begin *)
module X =
  let _ = 1

(* Explicit begin *)
module X = struct
  let _ = 1
end

(* Explicit begin with weird alignment *)
module X =
struct
  let _ = 1
end

module X =
  struct
    let _ = 1
  end

module X = Y

(* Access modifiers *)
private module Y =
  let a = 0

(* Module types *)
module type Y = sig
 type t
 val x : t
end

module type Z = (Arg : Y) -> sig val y : Arg.t end

(* Functors *)
module X = fun (Arg : Y) struct
 let y = Arg.x
end

(* Ascriptions *)
module X' = X : Z

open X Arg
