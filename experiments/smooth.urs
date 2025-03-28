module smooth set

def SmthSet : U₁ := Sh(CrtSp, Set)

-- Probe space (Cartesian spaces)
def CrtSp : U₀ := ℝ^n  -- Indexed by n : Nat

-- Constructors
def plt (n : Nat) (X : SmthSet) : Set := Plt(ℝ^n, X)
def precomp (n m : Nat) (X : SmthSet) (f : ℝ^m → ℝ^n) (φ : plt n X) : plt m X := φ ∘ f
def glue (n : Nat) (X : SmthSet) (U : OpenCover n) (φs : Π (i : I), plt (U i) X)
    (coh : Π (i j : I), Path (plt (U i ∩ U j) X) (φs i | U i ∩ U j) (φs j | U i ∩ U j))
  : plt n X := glue U φs coh

-- Eliminators
def eval (n : Nat) (X : SmthSet) (φ : plt n X) : X := φ
def germ (n : Nat) (X : SmthSet) (φ : plt n X) : PltGrm(ℝ^n, X) := germ φ

-- Computation rules
def precomp-id (n : Nat) (X : SmthSet) (φ : plt n X)
  : Path (plt n X) (precomp n n X id φ) φ := idp (plt n X) φ
def glue-eval (n : Nat) (X : SmthSet) (U : OpenCover n) (φs : Π (i : I), plt (U i) X) (coh : ...)
  : Path (plt (U i) X) (eval n X (glue U φs coh) | U i) (φs i) := idp (plt (U i) X) (φs i)

def Maps (A B : SmthSet) : SmthSet := Maps(A, B)

-- Constructors
def map (A B : SmthSet) (f : A → B) : Maps A B := λ (x : A), f x
def plot-map (U A B : SmthSet) (Φ : plt U (Maps A B)) : plt (U × A) B := λ (u, x), Φ u x

-- Eliminators
def app-map (A B : SmthSet) (Φ : Maps A B) (a : A) : B := Φ a
def unfold (U A B : SmthSet) (Φ : Maps U (Maps A B)) : Maps (U × A) B := λ (u, a), Φ u a

-- Computation rules
def map-β (A B : SmthSet) (f : A → B) (a : A)
  : Path B (app-map A B (map A B f) a) (f a) := idp B (f a)
def unfold-plot (U A B : SmthSet) (Φ : plt U (Maps A B)) (u : U) (a : A)
  : Path B ((unfold U A B (map U (Maps A B) (λ u, Φ u))) (u, a)) (Φ u a) := idp B (Φ u a)
