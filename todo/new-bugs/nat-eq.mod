mod NAT=1 {
 ex(EQL)
 ex(NAT)

 eq (NN1:NzNat = NN2:NzNat) = (NN1 == NN2) .

 -- this does not work
 eq (NN:NzNat = 0) = false .
}

eof
