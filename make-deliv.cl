(load "sysdef")
(excl:compile-system :chaosx :recompile t)
(excl:concatenate-system :chaosx "pignose.fasl")
(load "deliver")

