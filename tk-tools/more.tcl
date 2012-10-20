# chaos:more ?options? ?-title hdr? ?-text txt? - displays text in window
# options include
#   -title (default "Output")
#   -text (default "" - not really optional)
#   -height (default 24)
#   -width (default 80)
#   -font (default "default")
#   -class (default "More")
# this unfortunately forces focus-follows-pointer in these windows
#-------------------------------------------------------------------------------
proc chaos:more { args } {

  chaos:parse_args {
    {title Output}
    {text {}}
    {wrap char}
    {height 24}
    {width 80}
    {font default}
    {class More}
  }
  
  global chaos_more

  if {[info exists chaos_more(count)]} then {
    set chaos_more(count) [expr {$chaos_more(count) + 1}]
  } else {
    set chaos_more(count) 0
  }

  set w ".more$chaos_more(count)"

  toplevel $w -class $class
  wm title $w $title
  
  # using chaos:buttonbar for visual consistency, although we can't (easily)
  # set the commands with it (because they depend on the window name):
  
  chaos:buttonbar $w.b -default ok -buttons {
    {ok Done {}}
    {save Save {}}
    {print Print {}}
    {find {Find . . .} {}}
  }
  $w.b.ok configure -command "destroy $w"
  $w.b.save configure -command "chaos:more:save $w"
  $w.b.print configure -command "chaos:more:print $w"
  $w.b.find configure -width 8 -command "chaos:find -replace 0 $w.t"
  
  scrollbar $w.sb -relief flat -command "$w.t yview"
  text $w.t -yscrollcommand "$w.sb set" -setgrid true -wrap word \
    -height $height -wrap $wrap -width $width
  chaos:configure_font $w.t $font
  
  pack \
    $w.b \
    [chaos:rule $w] \
    -side bottom -fill x
  pack \
    $w.sb \
    [chaos:rule $w] \
    -side right -fill y
  pack \
    $w.t \
    -expand yes -fill both
  
  $w.t insert end $text
  
  $w.t mark set insert 1.0

  $w.t configure -state disabled ;# prevent its being edited
  
  # FOLLOWING BINDINGS SHOULD BE GENERALISED! and check J_PREFS(bindings)!
  #
  bind $w.t <Next> "chaos:more:pageup $w.t"
  bind $w.t <space> "chaos:more:pageup $w.t"
  bind $w.t <Control-v> "chaos:more:pageup $w.t"
  
  bind $w.t <Prior> "chaos:more:pagedown $w.t"
  bind $w.t <b> "chaos:more:pagedown $w.t"
  bind $w.t <Escape><v> "chaos:more:pagedown $w.t"
  
  bind $w <Any-Enter> "focus $w.t"
  
  # "cancel" and "ok" amount to the same thing for this window:
  chaos:default_button $w.b.ok $w.t
  chaos:cancel_button $w.b.ok $w.t
  
  return $w.t			;# so caller can insert things in it
}

# chaos:more:save w - prompts to save the content of a chaos:more window
#   NOTE: this adds a newline!  should check if ends in newline alr.
#-------------------------------------------------------------------------------

proc chaos:more:save { w } {
  set filename [chaos:fs]
  if {$filename == {}	} {
    return 1
  }
  # should do error checking
  set file [open $filename {w}]
  puts $file [$w.t get 1.0 end]
  close $file
}

# chaos:more:print w - prompts to print the content of a chaos:more window
#   command to use should be a preference!
# uses J_PREFS(printer)
#-------------------------------------------------------------------------------

proc chaos:more:print { w } {
  global env J_PREFS
  
  chaos:alert -title "Sorry!" -text {printing is not supported yet!}
#  append J_PREFS(printer) {}			;# make sure it's defined
#  if {"x$J_PREFS(printer)" == "x"} then {set J_PREFS(printer) "lp"}
#  
#  if [chaos:confirm -priority 100 -text "Print using lpr to $J_PREFS(printer)?"] {
#    # should do error checking
#    set file [open "|lpr -P$J_PREFS(printer)" {w}]
#    puts $file [$w.t get 1.0 end] nonewline
#    close $file
#  }
}

# chaos:more:pageup t - scrolls text widget t up
#   requires scrollbar to be sibling named "sb"
#   based on procedure by Paul Raines <raines@bohr.physics.upenn.edu>
#-------------------------------------------------------------------------------

proc chaos:more:pageup { t } {
  set sb "[winfo parent $t].sb"
  $t mark set insert "[lindex [$sb get] 3].0"
  $t yview insert
}

# chaos:more:pagedown t - scrolls text widget t down
#   requires scrollbar to be sibling named "sb"
#   based on procedure by Paul Raines <raines@bohr.physics.upenn.edu>
#-------------------------------------------------------------------------------

proc chaos:more:pagedown { t } {
  set sb "[winfo parent $t].sb"
  set currentstate [$sb get]
  
  # following is buggy if lines wrap:
  #
  set newlinepos [expr {[lindex $currentstate 2]-[lindex $currentstate 1]}]
  $t mark set insert "$newlinepos.0-2lines"
  $t yview insert
}
