(* Module for generating large random numbers in zarith. *)
(* https://en.wikipedia.org/wiki/Linear_congruential_generator#cite_note-LEcuyer99-10 *)

let () = Random.self_init ()

type generator =
  | LinearCongruentialGenerator of Z.t * Z.t * Z.t

type pseudorandom_number_generator = PRNG of Z.t * generator

let multiplier = Z.of_string "6364136223846793005"
let increment  = Z.one
let modulus    = Z.(of_int 2 ** 256)

(** [rand_z_get_prng s b] creates and returns a PRNG using the given seed. 
*)
let rand_z_get_prng s = 
  PRNG(s, LinearCongruentialGenerator(multiplier, increment, modulus))

(** [rand_z_from_prng g b] same as [rand_z] but it uses [g] as a generator 
    instead of the default one.
    Note that this function can be partially applied to get the same effect as
    [rand_z].
*)
let rand_z_from_prng g b =
  match !g with
  | PRNG(seed, LinearCongruentialGenerator(a, c, m)) ->
    let seed = Z.((a * seed + c) mod m) in
    let res = Z.(if seed < b then seed else seed mod b) in
    g := PRNG(seed, LinearCongruentialGenerator(a, c, m));
    res

let seed = Z.of_int64 (Random.int64 Int64.max_int)
let default_gen = ref (
  PRNG(seed,
       LinearCongruentialGenerator(multiplier, increment, modulus))
)

(** [rand_z b] returns a pseudo-randomly generated number between 0 (inclusive)
    and [b] (exclusive). 
    The PRNG behind the scene is a default one (with its seed generated using 
    ocaml's int64 PRNG)
*)
let rand_z b = rand_z_from_prng default_gen b