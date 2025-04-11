
(* Copyright (c) 2025 Groupoid Infinity *)

open List

let verbose = false
let trace = false

(* Universe grades: bosonic (0) or fermionic (1) in honor of Satyendra Nath Bose and Enrico Fermi *)
type grade = Bose | Fermi

let combine_grades (g1 : grade) (g2 : grade) : grade =
  match g1, g2 with
  | Bose, Bose -> Bose
  | Bose, Fermi -> Fermi
  | Fermi, Bose -> Fermi
  | Fermi, Fermi -> Bose

type exp =

  (* MLTT/HoTT Core *)
  | Universe of int * grade           (* U i g *)
  | Var of string                     (* x *)
  | Forall of string * exp * exp      (* Π(x:A).B *)
  | Lam of string * exp * exp         (* λx:A. b *)
  | App of exp * exp                  (* f a *)
  | Path of exp * exp * exp           (* Id_A(u,v) *)
  | Transport of exp * exp * exp      (* transport A p t *)

  (* Cohesive Types *)
  | SmthSet                           (* SmthSet *)
  | Plot of int * exp * exp           (* plt n X φ *)
  | Flat of exp                       (* ♭ A *)
  | Sharp of exp                      (* ♯ A *)
  | Shape of exp                      (* ℑ A *)
  | Bosonic of exp                    (* ◯ A *)

  (* Graded and Supergeometry *)
  | Tensor of exp * exp               (* A ⊗ B *)
  | SupSmthSet                        (* SupSmthSet *)

  (* Groupoids *)
  | Grpd of int                       (* Grpd n *)
  | Comp of int * exp * exp * exp     (* comp n G a b *)

  (* Spectra and Stable Homotopy *)
  | Spectrum                          (* Spectrum *)
  | Susp of exp                       (* Susp A *)
  | Wedge of exp * exp                (* A ∧ B *)
  | HomSpec of exp * exp              (* [A, B] *)

  (* TED-K *)
  | KU_G of exp * exp * exp           (* KU_G^τ(X; τ) *)
  | Qubit of exp * exp                (* [Config, Fred^0 H] *)
  | Linear of exp                     (* !A or Type_{lin} *)
  | AppQubit of exp * exp * exp       (* appQubit A Q x *)
  | FuseQubit of exp * exp * exp      (* fuseQubit q₁ q₂ (chan : H ⊗ H) *)
  | Config of int * exp               (* Config^n(X) *)
  | Braid of int * exp                (* BB_n *)

  (* Differential Cohomology *)
  | Forms of int * exp                (* Ω^n(X) *)
  | Diff of int * exp                 (* d ω *)
  | DiffKU_G of exp * exp * exp * exp (* DiffKU_G^τ(X; τ, conn) *)

type context = (string * exp) list

let string_of_grade = function
  | Bose -> "0" | Fermi -> "1"

let rec string_of_exp = function
  | Universe (i, g) -> "U_" ^ string_of_int i ^ "_" ^ string_of_grade g
  | Var x -> x
  | Forall (x, a, b) -> "Π(" ^ x ^ ":" ^ string_of_exp a ^ ")." ^ string_of_exp b
  | Lam (x, a, b) -> "λ" ^ x ^ ":" ^ string_of_exp a ^ "." ^ string_of_exp b
  | App (f, a) -> "(" ^ string_of_exp f ^ " " ^ string_of_exp a ^ ")"
  | Path (a, u, v) -> "Id_" ^ string_of_exp a ^ "(" ^ string_of_exp u ^ "," ^ string_of_exp v ^ ")"
  | Transport (a, p, t) -> "transport(" ^ string_of_exp a ^ "," ^ string_of_exp p ^ "," ^ string_of_exp t ^ ")"
  | SmthSet -> "SmthSet"
  | Plot (n, x, phi) -> "plt_" ^ string_of_int n ^ "(" ^ string_of_exp x ^ "," ^ string_of_exp phi ^ ")"
  | Flat a -> "♭(" ^ string_of_exp a ^ ")"
  | Sharp a -> "♯(" ^ string_of_exp a ^ ")"
  | Shape a -> "ℑ(" ^ string_of_exp a ^ ")"
  | Bosonic a -> "◯(" ^ string_of_exp a ^ ")"
  | Tensor (a, b) -> string_of_exp a ^ " ⊗ " ^ string_of_exp b
  | SupSmthSet -> "SupSmthSet"
  | Grpd n -> "Grpd_" ^ string_of_int n
  | Comp (n, g, a, b) -> "comp_" ^ string_of_int n ^ "(" ^ string_of_exp g ^ "," ^ string_of_exp a ^ "," ^ string_of_exp b ^ ")"
  | Spectrum -> "Spectrum"
  | Susp a -> "Susp(" ^ string_of_exp a ^ ")"
  | Wedge (a, b) -> string_of_exp a ^ " ∧ " ^ string_of_exp b
  | HomSpec (a, b) -> "[" ^ string_of_exp a ^ "," ^ string_of_exp b ^ "]"
  | KU_G (x, g, tau) -> "KU_" ^ string_of_exp g ^ "^" ^ string_of_exp tau ^ "(" ^ string_of_exp x ^ ")"
  | Qubit (c, h) -> "[" ^ string_of_exp c ^ "," ^ string_of_exp h ^ "]"
  | Config (n, x) -> "Config^" ^ string_of_int n ^ "(" ^ string_of_exp x ^ ")"
  | Braid (n, b) -> "BB_" ^ string_of_int n ^ "(" ^ string_of_exp b ^ ")"
  | Forms (n, x) -> "Ω^" ^ string_of_int n ^ "(" ^ string_of_exp x ^ ")"
  | Diff (n, omega) -> "d_" ^ string_of_int n ^ "(" ^ string_of_exp omega ^ ")"
  | DiffKU_G (x, g, tau, conn) -> "DiffKU_" ^ string_of_exp g ^ "^" ^ string_of_exp tau ^ "(" ^ string_of_exp x ^ "," ^ string_of_exp conn ^ ")"
  | Linear a -> "!" ^ string_of_exp a  (* Linear type as !A *)
  | AppQubit (a, q, x) -> "appQubit " ^ string_of_exp a ^ " " ^ string_of_exp q ^ " " ^ string_of_exp x
  | FuseQubit (q1, q2, chan) -> "fuseQubit (" ^ string_of_exp q1 ^ ") (" ^ string_of_exp q2 ^ ") (" ^ string_of_exp chan ^ ")"

let rec subst x s t =
  match t with
  | Var y -> if x = y then s else t
  | Forall (y, a, b) -> if x = y then t else Forall (y, subst x s a, subst x s b)
  | Lam (y, a, b) -> if x = y then t else Lam (y, subst x s a, subst x s b)
  | App (f, a) -> App (subst x s f, subst x s a)
  | Path (a, u, v) -> Path (subst x s a, subst x s u, subst x s v)
  | Transport (a, p, t') -> Transport (subst x s a, subst x s p, subst x s t')
  | Flat a -> Flat (subst x s a)
  | Sharp a -> Sharp (subst x s a)
  | Shape a -> Shape (subst x s a)
  | Bosonic a -> Bosonic (subst x s a)
  | Tensor (a, b) -> Tensor (subst x s a, subst x s b)
  | Comp (n, g, a, b) -> Comp (n, subst x s g, subst x s a, subst x s b)
  | Susp a -> Susp (subst x s a)
  | Wedge (a, b) -> Wedge (subst x s a, subst x s b)
  | HomSpec (a, b) -> HomSpec (subst x s a, subst x s b)
  | KU_G (x', g, tau) -> KU_G (subst x s x', subst x s g, subst x s tau)
  | Qubit (c, h) -> Qubit (subst x s c, subst x s h)
  | Config (n, x') -> Config (n, subst x s x')
  | Braid (n, b) -> Braid (n, subst x s b)
  | Forms (n, x') -> Forms (n, subst x s x')
  | Diff (n, omega) -> Diff (n, subst x s omega)
  | DiffKU_G (x', g, tau, conn) -> DiffKU_G (subst x s x', subst x s g, subst x s tau, subst x s conn)
  | _ -> t

let rec infer (ctx : context) (e : exp) : exp =
  if verbose then Printf.printf "Infer: %s\n" (string_of_exp e);
  match e with
  | Universe (i, g) -> Universe (i + 1, Bose) (* U_i : U_{i+1} *)
  | Var x -> (match find_opt (fun (y, _) -> y = x) ctx with
             | Some (_, ty) -> ty
             | None -> raise (Failure ("Unbound variable: " ^ x)))
  | Forall (x, a, b) ->
      let a_ty = infer ctx a in
      (match a_ty with
       | Universe (i, g) | Linear (Universe (i, g)) ->
           let ctx' = (x, a) :: ctx in
           let b_ty = infer ctx' b in
           (match b_ty with
            | Universe (j, h) -> Universe (max i j, combine_grades g h)
            | _ -> raise (Failure "Forall body must be a type"))
       | _ -> raise (Failure "Forall domain must be a type or linear type"))
  | Lam (x, a, b) ->
      let a_ty = infer ctx a in
      (match a_ty with
       | Universe _ ->  (* Ensure 'a' is a type by checking its type is a universe *)
           let ctx' = (x, a) :: ctx in
           let b_ty = infer ctx' b in
           Forall (x, a, b_ty)
       | _ -> raise (Failure ("Lambda domain must be a type, got: " ^ string_of_exp a_ty)))
  | App (f, arg) ->
      (match infer ctx f with
       | Forall (x, a, b) -> check ctx arg a; subst x arg b
       | ty -> raise (Failure ("Application requires a Forall type, got: " ^ string_of_exp ty)))
  | Path (a, u, v) ->
      let a_ty = infer ctx a in
      (match a_ty with
       | Universe _ -> check ctx u a; check ctx v a; Universe (0, Bose)
       | _ -> Universe (0, Bose))
  | Transport (a, p, t) ->
      let a_ty = infer ctx a in
      (match a_ty with
       | Forall (_, x, b) ->
           let p_ty = infer ctx p in
           (match p_ty with
            | Path (x', u, v) when equal ctx x x' -> check ctx t (subst "_dummy" u b); subst "_dummy" v b
            | _ -> raise (Failure "Transport path type mismatch"))
       | _ -> raise (Failure "Transport requires a dependent type"))
  | SmthSet -> Universe (0, Bose)
  | Plot (n, x, phi) ->
      check ctx x SmthSet;
      check ctx phi (Forall ("_", Universe (n, Bose), x));
      SmthSet
  | Flat a -> let _ = check ctx a (Universe (0, Bose)) in Universe (0, Bose)
  | Sharp a -> let _ = check ctx a (Universe (0, Bose)) in Universe (0, Bose)
  | Shape a -> let _ = check ctx a (Universe (0, Bose)) in Universe (0, Fermi)
  | Bosonic a -> let _ = check ctx a (Universe (0, Fermi)) in Universe (0, Bose)
  | Tensor (a, b) ->
      let a_ty = infer ctx a in
      let b_ty = infer ctx b in
      (match a_ty, b_ty with
       | Universe (i, g1), Universe (j, g2) -> Universe (max i j, if g1 = Fermi || g2 = Fermi then Fermi else Bose)
       | _ -> raise (Failure "Tensor requires types"))
  | SupSmthSet -> Universe (0, Fermi)
  | Grpd n -> Universe (0, Bose)
  | Comp (n, g, a, b) ->
      check ctx g (Grpd n);
      check ctx a (Grpd (n-1));
      check ctx b (Grpd (n-1));
      Grpd (n-1)
  | Spectrum -> Universe (0, Bose)
  | Susp a -> let _ = check ctx a Spectrum in Spectrum
  | Wedge (a, b) -> let _ = check ctx a Spectrum in let _ = check ctx b Spectrum in Spectrum
  | HomSpec (a, b) -> let _ = check ctx a Spectrum in let _ = check ctx b Spectrum in Spectrum
  | KU_G (x, r, tau) ->
    let x_ty = infer ctx x in
    (match x_ty with
     | Universe (i, g) -> raise (Failure "KU_G first argument must be a term, not a type")
     | ty ->
         check ctx ty (Universe (0, Bose));
         check ctx r (Universe (0, Bose));
         check ctx tau (Forall ("_", ty, Universe (0, Bose)));
         Universe (0, Bose))
  | Qubit (c, h) ->
      check ctx c (Universe (0, Bose));
      check ctx h (Universe (0, Bose));
      Spectrum
  | Linear a ->
      let a_ty = infer ctx a in
      (match a_ty with
       | Universe (i, g) -> Universe (i, g)
       | _ -> raise (Failure "Linear requires a type"))
  | AppQubit (a, q, x) ->
      check ctx q (Qubit (a, Var "H"));   (* q : [A, Fred^0 H] *)
      check ctx x a;                      (* x : A *)
      Var "H"                             (* Result : H *)
  | FuseQubit (q1, q2, chan) ->
      check ctx q1 (Qubit (Var "Config", Var "H"));
      check ctx q2 (Qubit (Var "Config", Var "H"));
      check ctx chan (Tensor (Var "H", Var "H"));                            (* Channel : H ⊗ H *)
      Tensor (Qubit (Var "Config", Var "H"), Qubit (Var "Config", Var "H"))  (* Result : Qubit ⊗ Qubit *)
  | Config (n, x) ->
    check ctx x (Universe (0, Bose));     (* x : U_0_0 *)
    Universe (0, Bose)                    (* Config^n(X) : U_0_0 *)
  | Braid (n, b) -> check ctx b (Grpd 1); Grpd 1
  | Forms (n, x) -> check ctx x SmthSet; Universe (0, Bose)
  | Diff (n, omega) -> check ctx omega (Forms (n, Var "X")); Forms (n+1, Var "X")
  | DiffKU_G (x, g, tau, conn) ->
      check ctx x SmthSet;
      check ctx g (Grpd 1);
      check ctx tau (Forall ("_", x, Grpd 1));
      check ctx conn (Forms (1, x));
      Spectrum

and check (ctx : context) (e : exp) (ty : exp) : unit =
  if trace then Printf.printf "Check: %s : %s\n" (string_of_exp e) (string_of_exp ty);
  let inferred = infer ctx e in
  if equal ctx inferred ty then ()
  else raise (Failure (Printf.sprintf "Type mismatch: expected %s, got %s" (string_of_exp ty) (string_of_exp inferred)))

and equal (ctx : context) (t1 : exp) (t2 : exp) : bool =
  if verbose then Printf.printf "Equal: %s vs %s\n" (string_of_exp t1) (string_of_exp t2);
  match normalize ctx t1, normalize ctx t2 with
  | Universe (i1, g1), Universe (i2, g2) -> i1 = i2 && g1 = g2
  | Var x, Var y -> x = y
  | Forall (x, a1, b1), Forall (y, a2, b2) -> equal ctx a1 a2 && equal ((x, a1) :: ctx) b1 (subst y (Var x) b2)
  | Lam (x, a1, b1), Lam (y, a2, b2) when x = y ->  equal ctx a1 a2 && equal ((x, a1) :: ctx) b1 b2
  | Lam (x, a1, b1), Lam (y, a2, b2) -> equal ctx a1 a2 && equal ((x, a1) :: ctx) b1 (subst y (Var x) b2)
  | App (f1, a1), App (f2, a2) -> equal ctx f1 f2 && equal ctx a1 a2
  | Path (a1, u1, v1), Path (a2, u2, v2) -> equal ctx a1 a2 && equal ctx u1 u2 && equal ctx v1 v2
  | Transport (a1, p1, t1), Transport (a2, p2, t2) -> equal ctx a1 a2 && equal ctx p1 p2 && equal ctx t1 t2
  | Flat a1, Flat a2 -> equal ctx a1 a2
  | Sharp a1, Sharp a2 -> equal ctx a1 a2
  | Shape a1, Shape a2 -> equal ctx a1 a2
  | SmthSet, SmthSet -> true
  | Bosonic a1, Bosonic a2 -> equal ctx a1 a2
  | Tensor (a1, b1), Tensor (a2, b2) -> equal ctx a1 a2 && equal ctx b1 b2
  | Comp (n1, g1, a1, b1), Comp (n2, g2, a2, b2) -> n1 = n2 && equal ctx g1 g2 && equal ctx a1 a2 && equal ctx b1 b2
  | Susp a1, Susp a2 -> equal ctx a1 a2
  | Wedge (a1, b1), Wedge (a2, b2) -> equal ctx a1 a2 && equal ctx b1 b2
  | HomSpec (a1, b1), HomSpec (a2, b2) -> equal ctx a1 a2 && equal ctx b1 b2
  | KU_G (x1, g1, tau1), KU_G (x2, g2, tau2) -> equal ctx x1 x2 && equal ctx g1 g2 && equal ctx tau1 tau2
  | Qubit (c1, h1), Qubit (c2, h2) -> equal ctx c1 c2 && equal ctx h1 h2
  | Config (n1, x1), Config (n2, x2) -> n1 = n2 && equal ctx x1 x2
  | Braid (n1, b1), Braid (n2, b2) -> n1 = n2 && equal ctx b1 b2
  | Forms (n1, x1), Forms (n2, x2) -> n1 = n2 && equal ctx x1 x2
  | Diff (n1, o1), Diff (n2, o2) -> n1 = n2 && equal ctx o1 o2
  | DiffKU_G (x1, g1, t1, c1), DiffKU_G (x2, g2, t2, c2) ->
      equal ctx x1 x2 && equal ctx g1 g2 && equal ctx t1 t2 && equal ctx c1 c2
  | _ -> t1 = t2

and normalize (ctx : context) (e : exp) : exp =
  let rec reduce e =
    match e with
    | App (Lam (x, _, b), a) -> subst x a b
    | Transport (Forall (x, a, b), Path (_, u, v), t) -> subst x v (subst x u b)
    | _ -> e
  in
  let e' = reduce e in
  if e = e' then e else normalize ctx e'  (* Syntactic equality check *)


let config = Config (1, SmthSet)
let mzm_type = Linear (Universe (0, Bose))
let mzm_fusion_rule = Forall ("m1", mzm_type, Forall ("m2", mzm_type, Forall ("c", Universe (0, Bose), Universe (0, Bose))))
let ctx = [
  ("e", Lam ("x", SmthSet, KU_G (Var "x", Grpd 1, Var "τ")));
  ("τ", Forall ("_", SmthSet, Universe (0, Bose)));
  ("γ", mzm_type);
  ("H", Universe (0, Bose));
  ("SmthSet", Universe (0, Bose));
  ("config", Config (1, SmthSet));
  ("Config", Universe (0, Bose));
  ("1", Universe (0, Bose));
  ("refl", Path (Universe (0, Bose), Var "1", Var "1"));
  ("qubit_1", Var "H");
  ("MZMFusionRule", mzm_fusion_rule)
]

let mzm_state =
  Forall ("c", Config (1, SmthSet),
    Linear (Forall ("m", mzm_type,
      KU_G (Var "c", SmthSet, Lam ("_", Config (1, SmthSet), Grpd 1)))))

let fuse_mzm =
  Lam ("m₁", mzm_type,
    Lam ("m₂", mzm_type,
      Forall ("c", Universe (0, Bose),
        App (App (Var "MZMFusionRule", Var "m₁"), Var "m₂"))))

let resolve_mzm =
  Forall ("p", Forall ("c", Universe (0, Bose), App (App (Var "MZMFusionRule", Var "γ"), Var "γ")),
    Qubit (Config (1, SmthSet), Var "H"))

let fuse_mzm_state =
  Lam ("s₁", App (Var "MZMState", Var "c"),
    Lam ("s₂", App (Var "MZMState", Var "c"),
      Lam ("p₁", Forall ("m", mzm_type, KU_G (Var "c", SmthSet, Lam ("_", Universe (0, Bose), Grpd 1))),
        Lam ("p₂", Forall ("m", mzm_type, KU_G (Var "c", SmthSet, Lam ("_", Universe (0, Bose), Grpd 1))),
          FuseQubit (Var "q₁", Var "q₂", Tensor (Var "1", Var "1"))))))

let test_type ctx (term : exp) (expected_type : exp) (name : string) : unit =
    Printf.printf "TEST ";
    try let inferred_type = infer ctx term in
        if equal ctx inferred_type expected_type then
            Printf.printf "OK> %s = %s : %s\n" name (string_of_exp term) (string_of_exp inferred_type)
        else (
            Printf.printf "ERROR>\nTerm: %s\nInferred: %s\nExpected: %s\n" (string_of_exp term) (string_of_exp inferred_type) (string_of_exp expected_type);
            raise (Failure "Type mismatch")
        )
    with Failure msg -> Printf.printf "Error in %s: %s\n" name msg

let test_term ctx (term : exp) (expected_type : exp) (name : string) : unit =
    Printf.printf "TEST ";
    try if equal ctx term expected_type then
            Printf.printf "OK> %s = %s\n" name (string_of_exp term)
        else (
            Printf.printf "ERROR>\nTerm: %s\nExpected: %s\n" (string_of_exp term) (string_of_exp expected_type);
            raise (Failure "Term mismatch")
        )
    with Failure msg -> Printf.printf "Error in %s: %s\n" name msg

let () =
    test_type ctx mzm_state (Universe (1,Bose))  "mzm_state";
    test_type ctx config (Universe (0, Bose)) "config";
    test_term ctx (Var "MZMFusionRule") (Var "MZMFusionRule") "fusion";
    test_term ctx fuse_mzm fuse_mzm "fuse_mzm";
    test_term ctx fuse_mzm_state fuse_mzm_state "fuse_mzm_state";
    test_type ctx mzm_fusion_rule (Universe (1, Bose)) "mzm_fusion_rule";
    ()
