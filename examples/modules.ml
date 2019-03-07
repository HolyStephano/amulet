module Option =
  type option 'a =
    | Just of 'a
    | Nothing

  let map f m =
    match m with
    | Just x -> Just (f x)
    | Nothing -> Nothing

  module Helpers =
    let fmap = map

let _ = Option.Helpers.fmap (fun x -> x + 1) Option.Nothing
