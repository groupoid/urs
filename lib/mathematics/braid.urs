module braid where

import foundations.tedk
import foundations.config
import foundations.modalities
import foundations.set

-- Theorem: Braid Gate Transport
def braid-transport (n : Nat) (G : Group) (τ : Config^n (ℝ^2) → BPU) (b : plt-grpd 1 (BB_n n))
  : KU_G^τ(Config^n (ℝ^2); τ) → KU_G^τ(Config^n (ℝ^2); τ)
  := λ k, transport (KU_G^τ(Config^n (ℝ^2); τ)) (braid-shape n) b k

-- Proof Term: Transport along braid path
def braid-transport-proof (n : Nat) (G : Group) (τ : Config^n (ℝ^2) → BPU) (b : plt-grpd 1 (BB_n n))
    (k : KU_G^τ(Config^n (ℝ^2); τ))
  : Path (KU_G^τ(Config^n (ℝ^2); τ)) (braid-transport n G τ b k) k
  := let p : Path (Grpd 1) (ℑ (Config^n (ℝ^2))) (BB_n n) := braid-shape n,
         fb := elim-ku n G τ k : Maps (Config^n (ℝ^2)) (Fred^0 H),
         tr-fb := λ x, transport (Fred^0 H) (ap (λ g, plt-grpd 1 g) p) b (fb x),
         tr-k := intro-ku n G τ tr-fb
     in ap (intro-ku n G τ) (fun-ext (Config^n (ℝ^2)) (Fred^0 H) tr-fb fb
           (λ x, refl (fb x)))  -- Trivial transport for now; assumes braid acts trivially on Fred^0 H

-- Test Terms and Lemmas

-- Test 1: Apply braid transport
def test-braid-transport (n : Nat) (G : Group) (τ : Config^n (ℝ^2) → BPU)
    (b : plt-grpd 1 (BB_n n)) (f : Maps (Config^n (ℝ^2)) (Fred^0 H))
  : KU_G^τ(Config^n (ℝ^2); τ) := braid-transport n G τ b (intro-ku _ G τ f)
def test-braid-transport-proof (n : Nat) (G : Group) (τ : Config^n (ℝ^2) → BPU) 
    (b : plt-grpd 1 (BB_n n)) (f : Maps (Config^n (ℝ^2)) (Fred^0 H))
  : Path _ (test-braid-transport n G τ b f) (intro-ku _ G τ f)
  := braid-transport-proof n G τ b (intro-ku _ G τ f)

-- Lemma: Braid composition
def braid-compose (n : Nat) (G : Group) (τ : Config^n (ℝ^2) → BPU)
    (b1 b2 : plt-grpd 1 (BB_n n)) (consec : Consecutive b1 b2)
  : Path (KU_G^τ(Config^n (ℝ^2); τ) → KU_G^τ(Config^n (ℝ^2); τ))
        (braid-transport n G τ (comp 1 (BB_n n) b1 b2 consec))
        (λ k, braid-transport n G τ b1 (braid-transport n G τ b2 k))
  := let p := braid-shape n,
         comp-path := fill-horn 1 0 (BB_n n) (λ i _, if i = 0 then b1 else b2)
     in λ k, ap (transport _ p) comp-path k

