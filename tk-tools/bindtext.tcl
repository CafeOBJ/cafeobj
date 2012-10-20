
######################################################################
# chaos:selection_if_any - return selection if it exists, else {}
#   this is from kjx@comp.vuw.ac.nz (R. James Noble)
#   defined elsewhere, but copied here so the bindings libraries
#   don't depend on jtkutils
######################################################################

if {[info procs chaos:selection_if_any] == {}} {
  proc chaos:selection_if_any {} {
    if {[catch {selection get} s]} {return ""} {return $s}
  }
}

######################################################################
####
###  GENERAL BINDING ROUTINES
####
######################################################################

######################################################################
# chaos:tb:init - initialise info for bindings
######################################################################

proc chaos:tb:init { {t Text} } {
  global Chaos_PREFS env
  if {! [info exists Chaos_PREFS(typeover)]} {set Chaos_PREFS(typeover) 1}
  switch -exact $Chaos_PREFS(bindings) {
    basic {
      chaos:tb:basic_init $t
    }
    emacs {
      chaos:tb:emacs_init $t
    }
    edt {
      chaos:tb:edt_init $t
    }
    vi {
      chaos:tb:vi_init $t
    }
  }

  # read in user's supplementary text bindings
  chaos:source_config textbindings.tcl
}

######################################################################
# chaos:tb:no_op - do nothing
######################################################################

proc chaos:tb:no_op { args } {
  return 0
}

######################################################################
# chaos:tb:beep W - beep
######################################################################

proc chaos:tb:beep { W args } {
  chaos:beep $W
  return 0
}

######################################################################
# chaos:tb:move W index - move, possibly clearing selection and resetting state
######################################################################

proc chaos:tb:move { W index } {
  
  # clear current selection:
  $W tag remove sel 1.0 end
  chaos:text:move $W $index
}

######################################################################
# chaos:tb:clear_selection W - clear the selection in widget W
######################################################################

proc chaos:tb:clear_selection { W args } {
  $W tag remove sel 1.0 end
}

######################################################################
# chaos:tb:select_all W - select all text in widget W
######################################################################

proc chaos:tb:select_all { W args } {
  $W tag add sel 1.0 end
}

######################################################################
# chaos:tb:is_bol W - return true if insert is at beginning of line
#   from Achim Bohnet <ach@rosat.mpe-garching.mpg.de>
######################################################################

proc chaos:tb:is_bol { W } {
  return [$W compare insert == "insert linestart"]
}

######################################################################
# chaos:tb:is_eol W - return true if insert is at end of line
#   from Achim Bohnet <ach@rosat.mpe-garching.mpg.de>
######################################################################

proc chaos:tb:is_eol { W } {
  return [$W compare insert == "insert lineend"]
}

######################################################################
# chaos:tb:is_first_line W - return true if insert is on top line
######################################################################

proc chaos:tb:is_first_line { W } {
  return [$W compare "insert linestart" == 1.0]
}

######################################################################
# chaos:tb:is_last_line W - return true if insert is on last line
######################################################################

proc chaos:tb:is_last_line { W } {
  return [$W compare "insert lineend" == end]
}

######################################################################
######################################################################
# ROUTINES TO SET UP TEXT BINDINGS
######################################################################
######################################################################

# chaos:tb:key_bind W - set up bindings to process keys
proc chaos:tb:key_bind { W args } {
  # get rid of a few default Tk bindings:
  foreach binding {
    <Control-Key-v> <Control-Key-d> <Control-Key-h> <Any-Key>
    <Key-Delete> <Key-BackSpace> <Key-Return>
  } {
    bind $W $binding {}
  }
  # and create null bindings for modifiers, so they don't trigger commands:
  foreach binding {
    <Shift_L> <Shift_R> <Control_L> <Control_R> <Caps_Lock>
    <Shift_Lock> <Meta_L> <Meta_R> <Alt_L> <Alt_R>
  } {
    bind $W $binding { }
  }
  bind $W <Key>			{chaos:tkb:process_key %W "" %K %A}
  bind $W <Shift-Key>		{chaos:tkb:process_key %W "" %K %A}
  bind $W <Control-Key>		{chaos:tkb:process_key %W Control %K %A}
  
  # Compose (Multi_key) key support:
  bind $W <Multi_key>		{ }
  bind $W <Multi_key><Any-Key>	{chaos:tc:start_sequence %W %K %A}
  bind $W <Multi_key><Any-Key><Any-Key> \
  				{chaos:tc:finish_sequence %W %K %A}
  bind $W <Multi_key><Any-KeyRelease><Any-Key> \
    				{chaos:tc:start_sequence %W %K %A}
  bind $W <Multi_key><Any-Key><Any-Key> \
  				{chaos:tc:finish_sequence %W %K %A}
  bind $W <Multi_key><Any-Key><Any-KeyRelease><Any-Key> \
  				{chaos:tc:finish_sequence %W %K %A}
  bind $W <Multi_key><Any-KeyRelease><Any-Key><Any-KeyRelease><Any-Key> \
  				{chaos:tc:finish_sequence %W %K %A}

}

# jtextkeys.tcl - support for Text keyboard bindings
# 
# Copyright 1992-1994 by Jay Sekora.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 
# for non-profit, noncommercial use.
  
######################################################################
# chaos:tkb:mkmap w map next {{key command ?args?}...} - set up pseudo-binding
#   Note that key includes modifier
######################################################################

proc chaos:tkb:mkmap { w map next bindings } {
  global chaos_teb
  
  set chaos_teb(tkm_next,$w,$map) $next
  foreach list $bindings {
    set key [lindex $list 0]
    set command [lreplace $list 0 0]
    
    set chaos_teb(tkm,$w,$map,$key) $command
  }
}

######################################################################
# chaos:tkb:process_key W mod K A - process keystrokes
######################################################################

proc chaos:tkb:process_key {W mod K A} {
  global chaos_teb
  
  set chaos_teb(next_keymap,$W) ""		;# some bindings change this
  
  if {"x$mod" != "x"} {
    set K "$mod-$K"
    set default "$mod-DEFAULT"
  } else {
    set default "DEFAULT"
  }
  
  # if this widget hasn't been used before, set its keymap from default
  if {! [info exists chaos_teb(keymap,$W)]} {
    set chaos_teb(keymap,$W) $chaos_teb(keymap,Text)
  }
  # if no last command, set it to {}
  if {! [info exists chaos_teb(last_command,$W)]} {
    set chaos_teb(last_command,$W) {}
  }
  set map $chaos_teb(keymap,$W)

  if [info exists chaos_teb(tkm,$W,$map,$K)] {
    # specific action for this widget
    set command $chaos_teb(tkm,$W,$map,$K)
    eval $command [list $W $K $A]
  } else {
    if [info exists chaos_teb(tkm,Text,$map,$K)] {
      # specific binding for all Text widgets
      set command $chaos_teb(tkm,Text,$map,$K)
      eval $command [list $W $K $A]
    } else {
      if [info exists chaos_teb(tkm,$W,$map,$default)] {
        # default key action for this widget
        set command $chaos_teb(tkm,$W,$map,$default)
        eval $command [list $W $K $A]
      } else {
        # default key action for Text widgets
        set command $chaos_teb(tkm,Text,$map,$default)
        eval $command [list $W $K $A]
      }
    }
  }
  set chaos_teb(last_command,$W) $command
  
  # if a binding hasn't explicitly chosen a different keymap for the next
  #   key, switch to the default next keymap for this keymap:
  if {"x$chaos_teb(next_keymap,$W)" == "x"} {
    if [info exists chaos_teb(tkm_next,$W,$map)] {
      set chaos_teb(next_keymap,$W) $chaos_teb(tkm_next,$W,$map)
    } else {
      set chaos_teb(next_keymap,$W) $chaos_teb(tkm_next,Text,$map)
    }
  }
  set chaos_teb(keymap,$W) $chaos_teb(next_keymap,$W)
}

######################################################################
# chaos:tkb:new_mode mode W K A - change modes
######################################################################

proc chaos:tkb:new_mode { mode W K A } {
  global chaos_teb
  set chaos_teb(next_keymap,$W) $mode
}

######################################################################
# chaos:tkb:repeatable tclcode W - execute tclcode one or more times
######################################################################

proc chaos:tkb:repeatable { tclcode W args } {
  global chaos_teb
  
  # set up prefix/repeat information if this widget hasn't been used yet
  if {! [info exists chaos_teb(prefix,$W)]} {
    set chaos_teb(prefix,$W) 0
  }
  if {! [info exists chaos_teb(repeat_count,$W)]} {
    set chaos_teb(repeat_count,$W) 1
  }

  # special-case prefix == 1 and repeat_count == 0 for Emacs ^U:
  #
  if {$chaos_teb(prefix,$W) == 1 && $chaos_teb(repeat_count,$W) == 0} {
    set chaos_teb(repeat_count,$W) 4
  }
  
  set chaos_teb(prefix,$W) 0			;# no longer collectig digits
  for {set jri 0} {$jri < $chaos_teb(repeat_count,$W)} {incr jri} {
    uplevel 1 "eval [list $tclcode]"		;# variables in caller
  }
  set chaos_teb(repeat_count,$W) 1
}

######################################################################
# chaos:tkb:clear_count W - clear argument count
######################################################################

proc chaos:tkb:clear_count { W args } {
  global chaos_teb

  # set up prefix/repeat information if this widget hasn't been used yet
  if {! [info exists chaos_teb(prefix,$W)]} {
    set chaos_teb(prefix,$W) 0
  }
  if {! [info exists chaos_teb(repeat_count,$W)]} {
    set chaos_teb(repeat_count,$W) 1
  }

  set chaos_teb(repeat_count,$W) 1
  set chaos_teb(prefix,$W) 0
}

######################################################################
# chaos:tkb:start_number W K digit - start a numeric argument
#   invalid if not bound to (a sequence ending in) a digit key
######################################################################

proc chaos:tkb:start_number { W K digit } {
  global chaos_teb
  
  # set up prefix/repeat information if this widget hasn't been used yet
  if {! [info exists chaos_teb(prefix,$W)]} {
    set chaos_teb(prefix,$W) 0
  }
  if {! [info exists chaos_teb(repeat_count,$W)]} {
    set chaos_teb(prefix,$W) 1
  }

  set chaos_teb(prefix,$W) 1			;# collecting # prefix
  set chaos_teb(repeat_count,$W) [expr "$digit"]
}

######################################################################
# chaos:tkb:continue_number digit - continue a numeric argument
#   invalid if not bound to a digit key
######################################################################

proc chaos:tkb:continue_number { W K digit } {
  global chaos_teb
  
  # set up prefix/repeat information if this widget hasn't been used yet
  if {! [info exists chaos_teb(prefix,$W)]} {
    set chaos_teb(prefix,$W) 0
  }
  if {! [info exists chaos_teb(repeat_count,$W)]} {
    set chaos_teb(prefix,$W) 1
  }

  if {! $chaos_teb(prefix,$W)} {		;# (can start as well as continue)
    set chaos_teb(prefix,$W) 1	
    set chaos_teb(repeat_count,$W) 0
  }
  set chaos_teb(repeat_count,$W) [expr {($chaos_teb(repeat_count,$W)*10)+$digit}]
}

######################################################################
# chaos:tkb:paste_selection W - insert X selection into W
######################################################################

# chaos:tkb:paste_selection W - insert selection into W
#  (could also be used as mouse or key binding)
proc chaos:tkb:paste_selection { W K A } {
  set selection [chaos:selection_if_any]
  
  if {[string length $selection] != 0} {
    chaos:text:insert_string $W $selection
  }
}

######################################################################
###  TEXT SCROLLING COMMANDS - fragile - assume widget has a scrollbar
######################################################################
# fragile---assumes first word of yscrollcommand is name of scrollbar!
# should catch case of no yscrollcommand!
# ALSO---should handle arguments (scroll by line rather than windowful)

proc chaos:tkb:scroll_down { W K A } {
  global chaos_teb
  chaos:tkb:clear_count $W
  
  set yscrollcommand [lindex [$W configure -yscrollcommand] 4]
  set scrollbar [lindex $yscrollcommand 0]	;# cross fingers and hope!
  
  chaos:tb:move $W "[lindex [$scrollbar get] 3].0"
  $W yview insert				;# this is essential!
}

proc chaos:tkb:scroll_up { W K A } {
  global chaos_teb
  chaos:tkb:clear_count $W
  
   set yscrollcommand [lindex [$W configure -yscrollcommand] 4]
   set scrollbar [lindex $yscrollcommand 0]	;# cross fingers and hope!
 
   set currentstate [$scrollbar get]
   # following is buggy if lines wrap:
   set newlinepos [expr {[lindex $currentstate 2] - [lindex $currentstate 1]}]
   chaos:tb:move $W "$newlinepos.0-2lines"
   $W yview insert
}



######################################################################
### INSERTION COMMANDS
######################################################################

######################################################################
# chaos:tkb:insert_newline W K A - insert "\n" into W, clear arg flag
######################################################################

proc chaos:tkb:insert_newline { W K A } {
  global chaos_teb

  chaos:tkb:repeatable {
    chaos:text:insert_string $W "\n"
  } $W
}

######################################################################
# chaos:tkb:self_insert W K A - insert A into text widget W, clear arg flag
### (was chaos:tb:self_insert_nondigit
######################################################################

proc chaos:tkb:self_insert { W K A } {
  global chaos_teb

  if {"x$A" != "x"} {
    chaos:tkb:repeatable {
      chaos:text:insert_string $W $A
    } $W
  }
}

######################################################################
# chaos:tkb:self_insert_digit W K A - insert digit A into W, unless collecting arg
######################################################################

proc chaos:tkb:self_insert_digit { W K A } {
  global chaos_teb
    
  # set up prefix/repeat information if this widget hasn't been used yet
  if {! [info exists chaos_teb(prefix,$W)]} {
    set chaos_teb(prefix,$W) 0
  }

  if $chaos_teb(prefix,$W) {
    chaos:tkb:continue_number $W $K $A
    return 0
  } else {
    if {"x$A" != "x"} {
      chaos:tkb:repeatable {
        chaos:text:insert_string $W $A
      } $W
    }
  }
}

######################################################################
###  TEXT MOVEMENT COMMANDS
######################################################################

# chaos:tkb:bol W K A - move to start of line (ignores count)
proc chaos:tkb:bol { W K A } {
  chaos:tkb:repeatable {chaos:tb:move $W {insert linestart}} $W
}

# chaos:tkb:eol W K A - move to end of line (ignores count)
proc chaos:tkb:eol { W K A } {
  chaos:tkb:repeatable {chaos:tb:move $W {insert lineend}} $W
}

# chaos:tkb:up W K A - move up
proc chaos:tkb:up { W K A } {
  chaos:tkb:repeatable {chaos:tb:move $W {insert - 1 line}} $W
}

# chaos:tkb:down W K A - move down
proc chaos:tkb:down { W K A } {
  chaos:tkb:repeatable {chaos:tb:move $W {insert + 1 line}} $W
}

# chaos:tkb:left W K A - move left
proc chaos:tkb:left { W K A } {
  chaos:tkb:repeatable {chaos:tb:move $W {insert - 1 char}} $W
}

# chaos:tkb:right W K A - move right
proc chaos:tkb:right { W K A } {
  chaos:tkb:repeatable {chaos:tb:move $W {insert + 1 char}} $W
}

# chaos:tkb:bof W K A - move to beginning of file (widget)
proc chaos:tkb:bof { W K A } {
  chaos:tkb:repeatable {
    chaos:tb:move $W 0.0
  } $W
}

# chaos:tkb:eof W K A - move to end of file (widget)
proc chaos:tkb:eof { W K A } {
  chaos:tkb:repeatable {
    chaos:tb:move $W end
  } $W
}

# chaos:tkb:word_left W K A - move back one word
proc chaos:tkb:word_left { W K A } {
  chaos:tkb:repeatable {
    while {[$W compare insert != 1.0] &&
           [string match "\[ \t\n\]" [$W get {insert - 1 char}]]} {
      chaos:tb:move $W {insert - 1 char}
    }
    while {[$W compare insert != 1.0] &&
           ![string match "\[ \t\n\]" [$W get {insert - 1 char}]]} {
      chaos:tb:move $W {insert - 1 char}
    }
  } $W
}

# chaos:tkb:word_right W K A - move forward one word
proc chaos:tkb:word_right { W K A } {
  chaos:tkb:repeatable {
    while {[$W compare insert != end] &&
           [string match "\[ \t\n\]" [$W get insert]]} {
      chaos:tb:move $W {insert + 1 char}
    }
    while {[$W compare insert != end] &&
           ![string match "\[ \t\n\]" [$W get insert]]} {
      chaos:tb:move $W {insert + 1 char}
    }
  } $W
}

######################################################################
###  TEXT DELETION COMMANDS
######################################################################

# chaos:tkb:delete_right W K A - delete character at insert
proc chaos:tkb:delete_right { W K A } {
  
  if [$W compare insert != end] {
    global chaos_teb
    set chaos_teb(modified,$W) 1
    
    if {[chaos:text:insert_touches_selection $W]} {
      chaos:text:delete $W sel.first sel.last
      chaos:tkb:clear_count $W
      return 0
    }
    
    set delete_from [$W index insert]
    chaos:tkb:right $W $K $A	;# handles repeat count
    set delete_to [$W index insert]
    chaos:text:delete $W $delete_from $delete_to
  }
}

# chaos:tkb:delete_left W K A - delete character before insert
proc chaos:tkb:delete_left { W K A } {
  
  if [$W compare insert != 1.0] {
    global chaos_teb
    set chaos_teb(modified,$W) 1
    
    if {[chaos:text:insert_touches_selection $W]} {
      chaos:text:delete $W sel.first sel.last
      chaos:tkb:clear_count $W
      return 0
    }
    
    set delete_to [$W index insert]
    chaos:tkb:left $W $K $A		;# handles repeat count
    set delete_from [$W index insert]
    chaos:text:delete $W $delete_from $delete_to
  }
}

#### FOLLOWING TWO NEED TO HANDLE CUTBUFFER!

# chaos:tkb:delete_left_word W K A - move back one word
proc chaos:tkb:delete_left_word { W K A } {
  if [$W compare insert != 1.0] {
    global chaos_teb
    set chaos_teb(modified,$W) 1
  
    set delete_to [$W index insert]
    chaos:tkb:word_left $W $K $A	;# handles repeat count
    set delete_from [$W index insert]
    chaos:text:delete $W $delete_from $delete_to
  }
}

# chaos:tkb:delete_right_word W K A - move forward one word
proc chaos:tkb:delete_right_word { W K A } {
  if [$W compare insert != end] {
    global chaos_teb
    set chaos_teb(modified,$W) 1
  
    set delete_from [$W index insert]
    chaos:tkb:word_right $W $K $A	;# handles repeat count
    set delete_to [$W index insert]
    chaos:text:delete $W $delete_from $delete_to
  }
}

# jtextemacs.tcl - additional procedures for Emacs-like Text bindings
# 
# Copyright 1992-1994 by Jay Sekora.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 

# TO DO:
# ^L
# sentence-manipulation stuff
# case change commands, transposition commands
# commands to do with mark?
# word deletion - fix to use buffer
# generalise movement to copying-to-cutbuffer and deletion
# IMPROVE ENTRY BINDINGS
# literal-insert for entry

######################################################################
# chaos:tb:emacs_init t - set emacs bindings up for widget $t (possibly "Text")
######################################################################

proc chaos:tb:emacs_init { {t Text} } {
  global chaos_teb
  set chaos_teb(cutbuffer) {}
  set chaos_teb(dragscroll,txnd) 0
  set chaos_teb(dragscroll,delay) 50
  set chaos_teb(scanpaste_time) 0
  set chaos_teb(scanpaste_paste) 1
  
  set chaos_teb(keymap,$t) emacs-normal
  
  # in tk4, we need to make sure tkTextBind is called _before_
  #   chaos:tb:key_bind!
  chaos:tk4 {tkTextBind Enter}
  
  chaos:tb:key_bind $t
  chaos:tb:mouse_bind $t
  
  chaos:tkb:mkmap Text emacs-normal emacs-normal {
    {Control-slash		chaos:tb:select_all}
    {Control-backslash		chaos:tb:clear_selection}
    
    {Delete			chaos:tkb:delete_left}
    {BackSpace			chaos:tkb:delete_left}
    {Return			chaos:tkb:insert_newline}
    
    {Control-d			chaos:tkb:delete_right}
    
    {Up				chaos:tkb:up}
    {Down			chaos:tkb:down}
    {Left			chaos:tkb:left}
    {Right			chaos:tkb:right}
    
    {Control-p			chaos:tkb:up}
    {Control-n			chaos:tkb:down}
    {Control-b			chaos:tkb:left}
    {Control-f			chaos:tkb:right}
    
    {Home			chaos:tkb:bol}
    {End			chaos:tkb:eol}
    
    {Control-a			chaos:tkb:bol}
    {Control-e			chaos:tkb:eol}
    
    {Next			chaos:tkb:scroll_down}
    {Prior			chaos:tkb:scroll_up}
    
    {Control-v			chaos:tkb:scroll_down}
    
    {Control-k			chaos:tkb:e:kill_line}
    {Control-w			chaos:tkb:e:kill_region}
    {Control-y			chaos:tkb:e:yank}

    {Control-i			chaos:tkb:self_insert}
    {Control-j			chaos:tkb:self_insert}
    {Control-h			chaos:tkb:delete_left}
    
    {Control-space		chaos:tkb:e:set_mark_command}
    {Control-at			chaos:tkb:e:set_mark_command}
    
    {Control-g			chaos:tkb:clear_count}
    
    {1				chaos:tkb:self_insert_digit}
    {2				chaos:tkb:self_insert_digit}
    {3				chaos:tkb:self_insert_digit}
    {4				chaos:tkb:self_insert_digit}
    {5				chaos:tkb:self_insert_digit}
    {6				chaos:tkb:self_insert_digit}
    {7				chaos:tkb:self_insert_digit}
    {8				chaos:tkb:self_insert_digit}
    {9				chaos:tkb:self_insert_digit}
    {0				chaos:tkb:self_insert_digit}
    
    {Control-u			chaos:tkb:e:generic_arg}
    
    {Control-q			chaos:tkb:new_mode emacs-literal}
    {Control-x			chaos:tkb:new_mode emacs-control-x}
    {Escape			chaos:tkb:new_mode emacs-escape}
    
    {Control-DEFAULT		chaos:tb:no_op}
    {DEFAULT			chaos:tkb:self_insert}
    {Shift-DEFAULT		chaos:tkb:self_insert}
  }
  
  chaos:tkb:mkmap Text emacs-literal emacs-normal {
    {DEFAULT			chaos:tkb:self_insert}
    {Shift-DEFAULT		chaos:tkb:self_insert}
    {Control-DEFAULT		chaos:tkb:self_insert}
    {Meta-DEFAULT		chaos:tkb:self_insert}
  }
  
  chaos:tkb:mkmap Text emacs-control-x emacs-normal {
    {Control-g			chaos:tkb:clear_count}
    {Control-x			chaos:tkb:e:exchange_point_and_mark}
    
    {DEFAULT			chaos:tkb:clear_count}
    {Shift-DEFAULT		chaos:tkb:clear_count}
    {Control-DEFAULT		chaos:tkb:clear_count}
    {Meta-DEFAULT		chaos:tkb:clear_count}
  }
  
  chaos:tkb:mkmap Text emacs-escape emacs-normal {
    {less			chaos:tkb:bof}
    {greater			chaos:tkb:eof}
    {b				chaos:tkb:word_left}
    {f				chaos:tkb:word_right}
    {v				chaos:tkb:scroll_up}
    {w                          chaos:tkb:e:copy_region}
    {Delete			chaos:tkb:delete_left_word}
    {BackSpace			chaos:tkb:delete_left_word}
    {d				chaos:tkb:delete_right_word}
    
    {1				chaos:tkb:start_number}
    {2    			chaos:tkb:start_number}
    {3    			chaos:tkb:start_number}
    {4    			chaos:tkb:start_number}
    {5    			chaos:tkb:start_number}
    {6    			chaos:tkb:start_number}
    {7    			chaos:tkb:start_number}
    {8    			chaos:tkb:start_number}
    {9    			chaos:tkb:start_number}
    {0    			chaos:tkb:start_number}
    
    {Control-g			chaos:tkb:clear_count}
    
    {DEFAULT			chaos:tb:no_op}
    {Shift-DEFAULT		chaos:tb:no_op}
    {Control-DEFAULT		chaos:tb:no_op}
    {Meta-DEFAULT		chaos:tb:no_op}
  }
}

######################################################################
# chaos:tkb:e:generic_arg - start generic argument
#   kind of clumsy: set repeat count to four, or multiply by four
######################################################################

proc chaos:tkb:e:generic_arg { W args } {
  global chaos_teb
  
  # set up prefix/repeat information if this widget hasn't been used yet
  if {! [info exists chaos_teb(prefix,$W)]} {
    set chaos_teb(prefix,$W) 0
  }
  if {! [info exists chaos_teb(repeat_count,$W)]} {
    set chaos_teb(repeat_count,$W) 1
  }

  if {$chaos_teb(prefix,$W) == 1 && $chaos_teb(repeat_count,$W) == 0} {
    set chaos_teb(repeat_count,$W) 16		;# ^U^U -> 4*4
    return
  }
  if {$chaos_teb(prefix,$W) == 0} {
    set chaos_teb(prefix,$W) 1
    set chaos_teb(repeat_count,$W) 0		;# special; -> 4 in repeatable
    return
  }
  set chaos_teb(repeat_count,$W) [expr {$chaos_teb(repeat_count,$W)*4}]
}

######################################################################
###  TEXT EMACS DELETION COMMANDS
######################################################################

# chaos:tkb:e:kill_line W K A - delete insert to end-of-line, setting cutbuffer
#   (arg handled by called procedure)
proc chaos:tkb:e:kill_line { W K A } {
  global chaos_teb
  set chaos_teb(modified,$W) 1
  
  # set up prefix/repeat information if this widget hasn't been used yet
  if {! [info exists chaos_teb(prefix,$W)]} {
    set chaos_teb(prefix,$W) 0
  }
  if {! [info exists chaos_teb(repeat_count,$W)]} {
    set chaos_teb(repeat_count,$W) 1
  }

  # Append to cutbuffer if previous command was line-kill; otherwise
  #   start with new cutbuffer:
  set my_name [lindex [info level 0] 0]
  if {! [string match $my_name $chaos_teb(last_command,$W)]} {
    set chaos_teb(cutbuffer) {}
  }
  
  # special-case prefix == 1 and repeat_count == 0 for Emacs ^U^U:
  #
  if {$chaos_teb(prefix,$W) == 1 && $chaos_teb(repeat_count,$W) == 0} {
    set chaos_teb(repeat_count,$W) 4
  }
  
  # if no argument, DON'T kill "\n" unless it's only thing at insert
  #
  if {$chaos_teb(repeat_count,$W) < 2} {
    chaos:tkb:clear_count $W			;# in case it's eg -1
    if {[$W index insert] == [$W index {insert lineend}]} then {
      append chaos_teb(cutbuffer) [$W get insert]
      chaos:text:delete $W insert {insert + 1 char}
    } else {
      append chaos_teb(cutbuffer) [$W get insert {insert lineend}]
      chaos:text:delete $W insert {insert lineend}
    }
  } else {
    # with argument, kill that many lines (including "\n")
    chaos:tkb:repeatable {
      append chaos_teb(cutbuffer) [$W get insert {insert lineend + 1 char}]
      chaos:text:delete $W insert {insert lineend + 1 char}
    } $W
  }
  
  set chaos_teb(repeat_count,$W) 1
}

# chaos:tkb:e:kill_region W K A - delete selected region, setting cutbuffer
###   emacs region shouldn't be conflated with Text selection!
proc chaos:tkb:e:kill_region { W K A } {
  global chaos_teb
  set chaos_teb(modified,$W) 1

  chaos:tkb:clear_count $W

  set chaos_teb(cutbuffer) {}
  catch {
    set chaos_teb(cutbuffer) [$W get sel.first sel.last]
    chaos:text:delete $W sel.first sel.last
  }
}

proc chaos:tkb:e:copy_region { W K A} {
  global chaos_teb
  set chaos_teb(modified,$W) 1

  chaos:tkb:clear_count $W

  set chaos_teb(cutbuffer) {}
  catch {
    set chaos_teb(cutbuffer) [$W get sel.first sel.last]
  }
}

# chaos:tkb:e:yank W K A - insert contents of cutbuffer
###   handling of argument needs changed---not count, but not ignored
proc chaos:tkb:e:yank { W K A } {
  global chaos_teb

  chaos:tkb:clear_count $W
  
  chaos:text:insert_string $W $chaos_teb(cutbuffer)
}

######################################################################
###  TEXT EMACS MARK COMMANDS
######################################################################

# chaos:tkb:e:set_mark_command W K A - set emacs mark at current insert point
proc chaos:tkb:e:set_mark_command { W K A } {
  $W mark set emacs_mark insert
}

# chaos:tkb:e:exchange_point_and_mark W K A - swap insert point and emacs mark
proc chaos:tkb:e:exchange_point_and_mark { W K A } {
  if {[lsearch [$W mark names] emacs_mark] != -1} {
    set mark [$W index emacs_mark]
    $W mark set emacs_mark insert
    chaos:tb:move $W $mark
  } else {
    error "The mark is not set in text widget $W."
  }
}

# deprecated alias for backwards-compatibility:

proc chaos:tb:emacs_bind { W } {
  chaos:tb:emacs_init $W
}

# jtextmouse.tcl - support for Text mouse bindings
# 
# Copyright 1992-1994 by Jay Sekora.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 
# for non-profit, noncommercial use.

# TO DO:
# ^L
# sentence-manipulation stuff
# case change commands, transposition commands
# commands to do with mark?
# word deletion - fix to use buffer
# generalise movement to copying-to-cutbuffer and deletion
# IMPROVE ENTRY BINDINGS
# literal-insert for entry


######################################################################
# routines to let scanning and pasting to double-up on the same button
# based on code by Tom Phelps <phelps@cs.berkeley.edu>
# modified by jay to make it a little easier to paste
######################################################################

# chaos:tmb:start_scan_or_paste W x y t - start a drag or paste, recording
#   current location and time so we can later decide whether to paste or drag
# BIND TO <ButtonPress-N>
proc chaos:tmb:start_scan_or_paste { W x y t } {
  global chaos_teb
  $W scan mark $y
  set chaos_teb(scanpaste,time) $t
  set chaos_teb(scanpaste,x) $x
  set chaos_teb(scanpaste,y) $y
  set chaos_teb(scanpaste,pasting) 1
}

# chaos:tmb:continue_scan W x y t - scan the entry, and mark the fact that
#   we're scanning, not pasting.  won't scan if the mouse has moved only
#   one pixel.
# BIND TO <BN-Motion>
proc chaos:tmb:continue_scan { W x y t } {
  global chaos_teb
  
  set xdiff [expr {abs($x - $chaos_teb(scanpaste,x))}]
  set ydiff [expr {abs($y - $chaos_teb(scanpaste,y))}]
  
  if {$xdiff >= 2 || $ydiff >= 2} {
    $W scan dragto $y
    set chaos_teb(scanpaste,pasting) 0
  }
}

# chaos:tmb:end_scan_or_paste W x y t - if we haven't been scanning, and it's
#   been less than 500ms since button-down, paste selection
# BIND TO <ButtonRelease-N>
proc chaos:tmb:end_scan_or_paste { W x y t } {
  global chaos_teb
  if {$chaos_teb(scanpaste,pasting) &&
      [expr {$t-$chaos_teb(scanpaste,time)}] < 500} {
    # chaos:tb:paste_selection $W
    catch {
      focus $W
      chaos:text:insert_string $W [selection get]
    }
  }
}

######################################################################
# routines to allow scrolling during text selection
# from raines@cgibm1.slac.stanford.edu (Paul E. Raines)
# modifications by js@bu.edu (Jay Sekora) to make it a little
#   harder to make a selection, so you don't do it accidentally
#   when you just want to move.
######################################################################

# chaos:tmb:move_sel W x y - move and begin a selection
proc chaos:tmb:move_sel { W x y t } {
  global chaos_teb tk_priv
  set chaos_teb(dragscroll,txnd) 0
  set chaos_teb(dragscroll,x) $x
  set chaos_teb(dragscroll,y) $y
  
  set my_name [lindex [info level 0] 0]
  set chaos_teb(last_command,$W) $my_name	;# solves Emacs ^K, click, ^K problem
  
  # clear current selection:
  $W tag remove sel 1.0 end

  # do what normal Tk binding does:
  set tk_priv(selectMode) char
  chaos:text:move $W @$x,$y
  $W mark set anchor insert
  if {[lindex [$W config -state] 4] == "normal"} {focus $W}
}

# chaos:tmb:move W x y - move, don't change selection
proc chaos:tmb:move { W x y t } {
  global chaos_teb
  set my_name [lindex [info level 0] 0]
  set chaos_teb(last_command,$W) $my_name	;# solves Emacs ^K, click, ^K problem
  
  chaos:text:move $W @$x,$y
  $W mark set anchor insert
  if {[lindex [$W config -state] 4] == "normal"} {focus $W}
}

# chaos:tmb:drag_sel W x y - begin dragging out selection
proc chaos:tmb:drag_sel { W x y t } {
  global chaos_teb
  
  set xdiff [expr {abs($x - $chaos_teb(dragscroll,x))}]
  set ydiff [expr {abs($y - $chaos_teb(dragscroll,y))}]
  
  if {$xdiff < 3 && $ydiff < 3} {
    return
  }
  
  if {$y > [winfo height $W]} {
    if {!$chaos_teb(dragscroll,txnd)} {
      after $chaos_teb(dragscroll,delay) chaos:tmb:extend_sel $W $x $y $t
    }
    set chaos_teb(dragscroll,txnd) 1
    set chaos_teb(dragscroll,direction) down
  } else {
    if {$y < 0} {
      if {!$chaos_teb(dragscroll,txnd)} {
        after $chaos_teb(dragscroll,delay) chaos:tmb:extend_sel $W $x $y $t
      }
      set chaos_teb(dragscroll,txnd) 1
      set chaos_teb(dragscroll,direction) up
    } else {
      set chaos_teb(dragscroll,txnd) 0
      set chaos_teb(dragscroll,direction) 0
    }
  }

   if {!$chaos_teb(dragscroll,txnd)} {
  	tk_textSelectTo $W @$x,$y
  }
}

# chaos:tmb:extend_sel W x y t - drag out a selection, scrolling if necessary
proc chaos:tmb:extend_sel { W x y t } {
  global chaos_teb

  if {$chaos_teb(dragscroll,txnd)} {
    if {$chaos_teb(dragscroll,direction) == "down"} {
      tk_textSelectTo $W sel.last+1l
      $W yview -pickplace sel.last+1l
    } else {
      if {$chaos_teb(dragscroll,direction) == "up"} {
        tk_textSelectTo $W sel.first-1l
        $W yview -pickplace sel.first-1l
      } else { return }
    }
    after $chaos_teb(dragscroll,delay) chaos:tmb:extend_sel $W $x $y $t
  }
}

# chaos:tmb:end_sel W - finish a selection
proc chaos:tmb:end_sel { W args } {
  global chaos_teb
  set chaos_teb(dragscroll,txnd) 0
}

######################################################################
# set up text mouse bindings
#   these supplement, rather than replace, the standard Tk bindings.
######################################################################

proc chaos:tb:mouse_bind { W } {
  global chaos_teb
  
  chaos:tk3 {				;# bindings are superfluous in Tk 4
    # mouse bindings (for motion and scrolling selections)
    bind $W <Button-1>		{chaos:tmb:move_sel %W %x %y %t}
    bind $W <Control-Button-1>	{chaos:tmb:move %W %x %y %t}
    bind $W <B1-Motion>		{chaos:tmb:drag_sel %W %x %y %t}
    bind $W <ButtonRelease-1>	{chaos:tmb:end_sel %W %x %y %t}
    
    # mouse bindings (for scanning and pasting)
    bind $W <Button-2>		{chaos:tmb:start_scan_or_paste %W %x %y %t}
    bind $W <B2-Motion>		{chaos:tmb:continue_scan %W %x %y %t}
    bind $W <ButtonRelease-2>	{chaos:tmb:end_scan_or_paste %W %x %y %t}
  
    # mouse bindings (for scanning and pasting)
    bind $W <Button-3>		{chaos:tmb:start_scan_or_paste %W %x %y %t}
    bind $W <B3-Motion>		{chaos:tmb:continue_scan %W %x %y %t}
    bind $W <ButtonRelease-3>	{chaos:tmb:end_scan_or_paste %W %x %y %t}
  }
}

#
#
#
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

proc chaos:get:term { t } {
  if { [chaos:text:has_selection $t]} {
     return [selection get]
  } elseif { [chaos:select:last_term $t] } {
     return [selection get]
  } esle {
     return ""
  }
}
