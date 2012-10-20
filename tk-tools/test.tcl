proc chaos:select:last_term { t } {
  set last [$t index end]
  set done 0
  set from ""
  chaos:tkb:repeatable {chaos:tb:move $t end} $t
  chaos:tkb:repeatable {chaos:tb:move $t {insert linestart}} $t

  while {!$done} {
    if {[string match "\[ \t\n\]" [ $t get insert]]} {
       if {[$t compare insert == 1.0]} {
          set done 1 
       } else {
          chaos:tkb:repeatable {chaos:tb:move $t {insert - 1 line}} $t
          chaos:tkb:repeatable {chaos:tb:move $t {insert linestart}} $t
       }
    } else {
       set from [$t index insert]
       set done 1
    }
  }
  # return $from
  if {$from != ""} {
     $t tag remove sel 0.0 $from
     $t tag add sel $from $last
     return 1
  } else {
     return 0
  }
}
