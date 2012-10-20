module SAKE {
  [ Spirit < SPList ]

  ops S W B : -> Spirit
  op _,_ : Spirit SPList -> SPList

  -- eq W , nil = S, W .
  eq S, W = W .
  eq W, B = S .
  -- eq S, S = S .

}

-- Q? S, S, W , B <-> .... <-> W B W B
--    S, S, S, W <=>  W, B, W B
