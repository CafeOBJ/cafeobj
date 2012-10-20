#*******************************************************************************
# Basic utils for Chaos TK interface
# * see `tool-kits.lisp' for corresponding LISP part.
#*******************************************************************************

# options: 
# NOTE: not used now
#-------------------------------------------------------------------------------
option add *Rule.relief sunken widgetDefault
option add *Rule.width 2 widgetDefault
option add *Rule.height 2 widgetDefault
option add *Rule.borderWidth 1 widgetDefault
option add *Filler.relief flat widgetDefault
option add *Filler.width 10 widgetDefault
option add *Filler.height 10 widgetDefault
option add *Rule.relief sunken widgetDefault
option add *Rule.width 2 widgetDefault
option add *Rule.height 2 widgetDefault
option add *Rule.borderWidth 1 widgetDefault
option add *Filler.relief flat widgetDefault
option add *Filler.width 10 widgetDefault
option add *Filler.height 10 widgetDefault

#===============================================================================
# - parse procedure options in -name value style
#===============================================================================

# chaos:parse_args arglist - parse arglist in parent procedure
#   arglist is a list of option names (without leading "-");
# this proc puts their values (if any) into variables (named after
#   the option name) in d parent procedure
# any element of arglist can also be a list consisting of an option
#   name and a default value.
#-------------------------------------------------------------------------------

proc chaos:parse_args { arglist } {
  upvar args args
  
  foreach pair $arglist {
    set option [lindex $pair 0]
    set default [lindex $pair 1]		;# will be null if not supplied
    set index [lsearch -exact $args "-$option"]
    if {$index != -1} {
      set index1 [expr {$index + 1}]
      set value [lindex $args $index1]
      uplevel 1 [list set $option $value]	;# caller's variable "$option"
      set args [lreplace $args $index $index1]
    } else {
      uplevel 1 [list set $option $default]	;# caller's variable "$option"
    }
  }
  return 0
}

# chaos:parse_argv arglist - parse application's argv (and update argc)
#   arglist is a list of option names (without leading "-");
# this proc puts their values (if any) into variables (named after
#   the option name) in the parent procedure
# any element of arglist can also be a list consisting of an option
#   name and a default value.
#-------------------------------------------------------------------------------

proc chaos:parse_argv { arglist } {
  global argv argc
  
  foreach pair $arglist {
    set option [lindex $pair 0]
    set default [lindex $pair 1]		;# will be null if not supplied
    set index [lsearch -exact $argv "-$option"]
    if {$index != -1} {
      set index1 [expr {$index + 1}]
      set value [lindex $argv $index1]
      uplevel 1 [list set $option $value]	;# caller's variable "$option"
      set argv [lreplace $argv $index $index1]
    } else {
      uplevel 1 [list set $option $default]	;# caller's variable "$option"
    }
  }
  set argc [llength $argv]
  return 0
}

#===============================================================================
# 
#===============================================================================

# chaos:buttonbar w ?options? - make a buttonbar packed in w
# options are:
#   -default (default none)
#   -padx (default 5)
#   -pady (default 5)
#   -orient (default horizontal)
#   -buttons (default {})
# syntax of button list is {{name text command} ... }
#-------------------------------------------------------------------------------

proc chaos:buttonbar {args} {
  chaos:parse_args {
    {default "(NONE)"}
    {padx 5}
    {pady 5}
    {orient horizontal}
    {font -*-helvetica-bold-r-normal--14-*}
    buttons
  }

  if {[llength $args] != 1} {
    tkerror {Improper arguments}
  }
  
  set newframe [lindex $args 0]
  
  if {$orient == "horizontal"} {
    set side right				;# for packing
  } else {
    set side bottom				;# for packing
  }

  frame $newframe
  if {$padx} {
    pack [chaos:filler $newframe -width $padx] -in $newframe -side left
    pack [chaos:filler $newframe -width $padx] -in $newframe -side right
  }
  if {$pady} {
    pack [chaos:filler $newframe -height $pady] -in $newframe -side top
    pack [chaos:filler $newframe -height $pady] -in $newframe -side bottom
  }
  
  foreach i $buttons {
    set name [lindex $i 0]
    set text [lindex $i 1]
    set command [lindex $i 2]

    set width [expr {[string length $text] + 1}]    
    if {$width < 8} {set width 8}
    
    set button $newframe.$name
    button $button -width $width -text $text -command $command \
    	   -font $font
    set border $newframe.border_$name
    frame $border -relief flat -borderwidth 1
    raise $button
    pack $button -in $border -padx 2 -pady 2
    pack $border -in $newframe -side $side -padx 2
    if [string match $default $name] {
      $border configure -relief sunken
    }
  }
  return $newframe
}

# chaos:tk4 - perform an action if running under Tk 4.0 or greater
#-------------------------------------------------------------------------------

proc chaos:tk4 { {command ""} } {
  global tk_version
  
  set major_version [lindex [split $tk_version .] 0]
  
  if {$major_version >= 4} {
    if [string length $command] {
      uplevel 1 [list eval $command]
    }
    return 1
  } else {
    return 0
  }
}

# chaos:tk3 - perform an action if running under Tk 3.X or earlier
#-------------------------------------------------------------------------------

proc chaos:tk3 { {command ""} } {
  global tk_version
  
  set major_version [lindex [split $tk_version .] 0]
  
  if {$major_version <= 3} {
    if [string length $command] {
      uplevel 1 [list eval $command]
    }
    return 1
  } else {
    return 0
  }
}

# chaos:current_focus - return current focus (assumes only one display!)
#-------------------------------------------------------------------------------

proc chaos:current_focus { {w .} } {
  global tk_version
  
  set major_version [lindex [split $tk_version .] 0]
  
  if {$major_version <= 3} {
    return [focus]
  } else {
    return [focus -lastfor $w]
  }
}

# chaos:wm_command ?args? - set the session client command
#-------------------------------------------------------------------------------
proc chaos:wm_command {{command ""}} {
  global argv0 argv
  
  if {[llength $command] == 0} {
    set command [concat $argv0 $argv]
  }
  
  wm command . $command
}


# chaos:new_toplevel prefix ?args? -
#   create a new toplevel, avoiding name conflicts
#-------------------------------------------------------------------------------

proc chaos:new_toplevel { prefix args } {
  set count 0
  
  while {[winfo exists $prefix$count]} {
    incr count
  }
  
  set tl $prefix$count
  toplevel $tl
  
  if {"x$args" != "x"} {
    eval [list $tl configure] $args
  }
  return $tl
}


# chaos:selection_if_any - return selection if it exists, else {}
#   this is from R. James Noble <kjx@comp.vuw.ac.nz>
#-------------------------------------------------------------------------------

proc chaos:selection_if_any {} {
  if {[catch {selection get} s]} {return ""} {return $s}
}

# chaos:beep w - "ring bell" in widget W
#-------------------------------------------------------------------------------

proc chaos:beep { w visible } {
  global chaos_beep
  
  set delay 100				;# should be a preference
  
  if { ! [info exists chaos_beep($w)] } {
    set chaos_beep($w) 0
  }
  
  if $chaos_beep($w) {
    return 1
  }
  set chaos_beep($w) 1			;# used so bells don't queue up
  
  if $visible {
    set fg black
    set bg white
    
    if ![catch {set fg [lindex [$w configure -foreground] 4]}] {
      catch {$w configure -foreground $bg}
      after $delay "catch {$w configure -foreground $fg}"
    }
    if ![catch {set bg [lindex [$w configure -background] 4]}] {
      catch {$w configure -background $fg}
      after $delay "catch {$w configure -background $bg}"
    }
    update
    after $delay "
      update
      set chaos_beep($w) 0
    "
  }
  if {! $visible} {
    chaos:tk4 {bell -displayof $w}
  }
  
  after $delay "set chaos_beep($w) 0"	;# allow processing future bells
  
  return 0
}

# chaos:no_selection - true if there is no selection
#-------------------------------------------------------------------------------

proc chaos:no_selection {} {
  if {[catch {selection get} s]} {return 1} {return 0}
}

#
# chaos:default_button button widget... - bind <Return> to default button
#   widget... is one or more widgets that can have the kbd focus
#-------------------------------------------------------------------------------

proc chaos:default_button { button args } {
  foreach w $args {
    bind $w <Return> "$button invoke"
  }
}

# chaos:cancel_button button widget... - set up bindings for cancel button
#   widget... is one or more widgets that can have the kbd focus
#-------------------------------------------------------------------------------

proc chaos:cancel_button { button args } {
  foreach w $args {
    bind $w <Control-c> "$button invoke"
    bind $w <Control-g> "$button invoke"
    bind $w <Meta-q> "$button invoke"
    bind $w <Meta-period> "$button invoke"
  }
}

# chaos:tab_ring widget... - bind Tab and Shift-Tab to cycle through widgets
#  widget... is the list of widgets to bind, in order
#-------------------------------------------------------------------------------
### It's unfortunate to have to hardwire Shift-Tab to Backtab, but there
### doesn't seem to be a <Backtab> X11 keysym.

proc chaos:tab_ring {args} {
  # index of last widget
  set last [expr {[llength $args] - 1}]
  
  for {set i 0} {$i < $last} {incr i} {
    set this [lindex $args $i]
    set next [lindex $args [expr {$i + 1}]]
    bind $this <Tab> "focus $next"
    bind $next <Shift-Tab> "focus $this"
  }
  
  # ... and bind last to focus on first:
  set this [lindex $args $last]
  set next [lindex $args 0]
  bind $this <Tab> "focus $next"
  bind $next <Shift-Tab> "focus $this"
}

# chaos:dialogue w - arrange to position window w near ctr of screen
#   mostly borrowed from /usr/local/lib/tk/dialog.tcl
#-------------------------------------------------------------------------------

proc chaos:dialogue { w autoposition} {

  if $autoposition {
    # first, display off-screen:
    wm withdraw $w		;# hide the window

    update idletasks		;# force geometry managers to run
    # calculate position:
    set x [expr [winfo screenwidth $w]/2 - [winfo reqwidth $w]/2 \
	    - [winfo vrootx [winfo parent $w]]]
    set y [expr [winfo screenheight $w]/3 - [winfo reqheight $w]/2 \
	    - [winfo vrooty [winfo parent $w]]]
    wm geom $w +$x+$y
    wm deiconify $w

    update idletasks		;# force geometry managers to run
    wm deiconify $w		;# display window
    wm focus $w
  }
}

proc chaos:dialog [info args chaos:dialogue] [info body chaos:dialogue]

# chaos:rule parent [args] - returns a rule suitable for parent
#       used as argument to a pack command
#-------------------------------------------------------------------------------

proc chaos:rule { {parent {}} args} {
  global chaos_rule

  if {$parent == "."} {set parent ""}	;# so "." doesn't give "..rule0"
  
  if {[info exists chaos_rule(count)]} then {
    set chaos_rule(count) [expr {$chaos_rule(count) + 1}]
  } else {
    set chaos_rule(count) 0
  }

  set rule "$parent.rule$chaos_rule(count)"
  frame $rule -class Rule
  if {$args != ""} {eval $rule configure $args}
  return $rule
}


# chaos:filler parent [args] - returns a filler frame suitable for parent
#       used as argument to a pack command
#-------------------------------------------------------------------------------

proc chaos:filler { {parent {}} args} {
  global chaos_filler

  if {$parent == "."} {set parent ""}	;# so "." doesn't give "..filler0"
  
  if {[info exists chaos_filler(count)]} then {
    set chaos_filler(count) [expr {$chaos_filler(count) + 1}]
  } else {
    set chaos_filler(count) 0
  }

  set filler "$parent.filler$chaos_filler(count)"
  frame $filler -class Filler
  if {$args != ""} {eval $filler configure $args}
  return $filler
}


# chaos:configure_font widget fontlist - use font from list, or default
#   tries to set widget's font to each font in list.
#   if a font is `default', tries to set to X default font.
#   if a font is {}, sets to courier 12-point.
#-------------------------------------------------------------------------------

proc chaos:configure_font { widget fontlist } {
  foreach font $fontlist {
    # try to use each font, until one is successful:
    if {$font == {default}} {
      set font [option get $widget font Font]
      if {$font == {}} {set font {*-courier-medium-r-normal--*-120-*}}
    }
    if {! [catch {$widget configure -font $font}]} {return}
  }
}

# chaos:configure_tag_font widget tag fontlist - use font from list, or default
#   tries to set tag's font to each font in list.
#   if a font is `default', tries to set to X default font.
#   if a font is {}, sets to courier 12-point.
#-------------------------------------------------------------------------------

proc chaos:configure_tag_font { widget tag fontlist } {
  foreach font $fontlist {
    # try to use each font, until one is successful:
    if {$font == {default}} {
      set font [option get $widget font Font]
      if {$font == {}} {set font {*-courier-medium-r-normal--*-120-*}}
    }
    if {! [catch {$widget tag configure $tag -font $font}]} {return}
  }
}

# chaos:confirm ?options? - Cancel/OK dialogue box
# options include
#   -title (default "Confirm")
#   -text (default "Are you sure?")
#   -priority (default 0)
#   -yesbutton (default "OK")
#   -nobutton (default "Cancel")
# returns true (1) on OK; false (0) on Cancel
#-------------------------------------------------------------------------------

global confirm_result

proc chaos:confirm { args } {
  chaos:parse_args {
    {title Confirm}
    {priority 0}
    {text "Are you sure?"}
    {yesbutton OK}
    {nobutton Cancel}
  }
  
  global confirm_result

  set old_focus [chaos:current_focus]	;# so we can restore original focus

  toplevel .confirm
  wm title .confirm $title
  
  message .confirm.msg -width 300 -anchor w -text $text
  chaos:buttonbar .confirm.b -default ok -buttons [format {
    {ok %s {set confirm_result 1; destroy .confirm}}
    {cancel %s {set confirm_result 0; destroy .confirm}}
  } $yesbutton $nobutton]
  
  pack .confirm.msg -side top -fill both -expand yes -padx 10 -pady 10
  pack [chaos:rule .confirm -width 200] -side top -fill x
  pack .confirm.b -side bottom -fill x
  
  chaos:dialogue .confirm 1		;# position in centre of screen

  focus .confirm
  chaos:default_button .confirm.b.ok .confirm
  chaos:cancel_button .confirm.b.cancel .confirm
  grab .confirm
  tkwait window .confirm
  focus $old_focus
  return $confirm_result
}

# chaos:alert ?options? - alert box
# options include
#   -title (default "Alert")
#   -text (default "Alert!" - not really optional)
#-------------------------------------------------------------------------------

proc chaos:alert { args } {
  chaos:parse_args {
    {title "Alert"}
    {text "Alert!"}
  }
  set old_focus [chaos:current_focus]	;# so we can restore original focus
  toplevel .alert
  wm title .alert $title
  
  message .alert.msg -width 300 -anchor w -text $text
  chaos:buttonbar .alert.b -default ok -buttons {{ok OK {destroy .alert}}}
  
  pack .alert.msg -side top -fill both -expand yes -padx 10 -pady 10
  pack [chaos:rule .alert -width 200] -side top -fill x
  pack .alert.b -side bottom -fill both
  
  chaos:dialogue .alert	1	;# position in centre of screen

  focus .alert
  chaos:default_button .alert.b.ok .alert
  grab .alert
  tkwait window .alert
  focus $old_focus
}

# chaos:prompt ?options? - prompt the user for information
# options are:
#   -text (default "Enter a value:")
#   -default (default "")
#   -cancelvalue (default "")
#   -file (default 0)
#   -title (default "Prompt")
# if $file, then the Tab key will do filename completion
#-------------------------------------------------------------------------------

proc chaos:prompt { args } {
  chaos:parse_args {
    {text "Enter a value:"}
    {default ""}
    {cancelvalue ""}
    {file 0}
    {title Prompt}
  }
  
  global chaos_prompt

  set old_focus [chaos:current_focus]	;# so we can restore original focus

  toplevel .pr
  wm title .pr $title
  
  message .pr.msg -width 300 -anchor w -text $text \
          -font -*-helvetica-bold-r-normal--14-*
  entry .pr.field -relief sunken -width 40 \
         -font -*-helvetica-medium-r-normal--12-*
  chaos:buttonbar .pr.b -default ok -buttons [format {
    {ok OK {set chaos_prompt(result) [.pr.field get]; destroy .pr}}
    {cancel Cancel {set chaos_prompt(result) {%s}; destroy .pr}}
  } $cancelvalue]

  pack .pr.msg -side top -fill both -expand yes -padx 10
  pack .pr.field -side top -padx 10 -pady 10
  pack .pr.b -side bottom -fill x
  pack [chaos:rule .pr -width 200] -side bottom -fill x

  .pr.field delete 0 end
  .pr.field insert end $default
  
  chaos:dialogue .pr 1		;# position in centre of screen

  if $file {
    bind .pr.field <Tab> {
      set f [%W get]
      %W delete 0 end
      %W insert end [chaos:expand_filename $f]
    }
  }
  chaos:default_button .pr.b.ok .pr.field
  chaos:cancel_button .pr.b.cancel .pr.field

  focus .pr.field
  grab .pr
  tkwait window .pr
  focus $old_focus
  return $chaos_prompt(result)
}

# chaos:prompt_font ?options? - prompt for a font (via xfontsel)
# options are:
#   -prompt (default "Font:", but currently ignored)
#   -pattern (default "*")
# usage of xfontsel (`quit' button) not obvious!
#-------------------------------------------------------------------------------

proc chaos:prompt_font { args } {
  chaos:parse_args {
    {prompt "Font:"}
    {pattern "*"}
  }
  return [exec xfontsel -pattern $pattern -print]
}

# chaos:prompt_tcl - prompt for a tcl command and execute it
#-------------------------------------------------------------------------------

proc chaos:prompt_tcl {} {
  global chaos_prompt_tcl
  append chaos_prompt_tcl(RESULT) {}

  set prompt_result [chaos:prompt \
    -text "Tcl Command:" -default $chaos_prompt_tcl(RESULT)]
  if {$prompt_result != {}} then {
    set chaos_prompt_tcl(RESULT) $prompt_result
    set result [uplevel #0 $chaos_prompt_tcl(RESULT)]
    set length [string length $result]
    if {$length == 0} {
      return
    }
    if {$length < 40 && ! [string match "*\[\t\r\]*" $result]} {
      chaos:alert -title "Tcl result" -text $result
      return
    } else {
      chaos:more -title "Result of Tcl command" -text $result
      return
    }
  }
}

# chaos:prompt_unix - prompt for a unix command and execute it
#-------------------------------------------------------------------------------

proc chaos:prompt_unix {} {
  global chaos_prompt_unix
  append chaos_prompt_unix(RESULT) {}

  set prompt_result [chaos:prompt \
    -text "Unix Command:" -default $chaos_prompt_unix(RESULT)]
  if {$prompt_result != {}} then {
    set chaos_prompt_unix(RESULT) $prompt_result
    set command $prompt_result
    set result [uplevel #0 exec $command < /dev/null]
    set length [string length $result]
    if {$length == 0} {
      chaos:alert -text "No output from $command."
      return
    }
    if {$length < 40 && ! [string match "*\[\t\r\]*" $result]} {
      chaos:alert -title "Command output" -text $result
      return
    } else {
      chaos:more -title "Output of $command" -text $result
      return
    }
  }
}


# record debugging information
#-------------------------------------------------------------------------------

proc chaos:debug { {string {chaos:debug called}} } {
  set w .debug_log
  
  if { ! [winfo exists $w] } {
    toplevel $w
    wm minsize . 10 10
    text $w.t -yscrollcommand "$w.sb set" -setgrid true
    scrollbar $w.sb -relief flat -command "$w.t yview"
    pack $w.sb $w.t -side right -fill y
  }
  
  set level [expr [info level] - 1]
  $w.t insert end "$string\n"
  switch -exact -- $level {
    0 {
      $w.t insert end "in top level.\n"
    }
    1 {
      $w.t insert end "in `[info level -1]'.\n"
    }
    default {
      $w.t insert end "in `[info level -1]'\n"
      $w.t insert end "  called from `[info level -2]'.\n"
    }
  }
  $w.t yview -pickplace end
}

#===============================================================================
# 			  Simple file selector panel
#===============================================================================

#------------------------------------------------------------------------------- 
# Fonts
#
set fileSelectMenuTitleFont -*-courier-medium-r-normal--14-140-*
set fileSelectMenuFont      -*-helvetica-medium-r-normal--12-120-*
set fileSelectEntryFont     -*-helvetica-medium-r-normal--12-120-*
set fileSelectTitleFont     -*-helvetica-bold-r-normal--12-120-*
set fileSelectListFont      -*-helvetica-medium-r-normal--12-120-*

#-------------------------------------------------------------------------------
# Colors
#
if { [winfo depth . ] > 1 } {
   set fileSelectBack SlateGray4
   set fileSelectFore white
   } else {
   set fileSelectBack gray
   set fileSelectFore white
  }   

#-------------------------------------------------------------------------------
# MakeFileSelectPanel
# generates simple file selctor box
# 
proc MakeFileSelectPanel { } {
  global fileSelectBack fileSelectFore
  global fileSelectMenuTitleFont fileSelectMenuFont
  global fileSelectTitleFont fileSelectEntryFont fileSelectListFont
  global FileSelectDirName FileSelectFileName

  if { ! [ winfo exists .file-select] } {
    # toplevel window
    toplevel .file-select
    wm title .file-select "File Selection"
    wm iconname  .file-select "File:Selection"
    # menu
    frame .file-select.menu -bd 4 -relief groove
    pack .file-select.menu -side top -fill x
    menubutton .file-select.menu.go -text "Go" -menu .file-select.menu.go.m \
    	-font $fileSelectMenuTitleFont -underline 0
    menu .file-select.menu.go.m -font $fileSelectMenuFont
    .file-select.menu.go.m add command -label "Home Directory" \
        -command { FileSelectcdto "~" ; FileSelectShowDir }
    .file-select.menu.go.m add command -label "Parent Directory" \
    	-command { FileSelectcdto ".." ; FileSelectShowDir }
    .file-select.menu.go.m add command -label "Root Directory" \
    	-command { FileSelectcdto "/" ; FileSelectShowDir }
    menubutton .file-select.menu.fileop -text "File Operations" \
    	-menu .file-select.menu.fileop.m -font $fileSelectMenuTitleFont \
    	-underline 4
    menu .file-select.menu.fileop.m -font $fileSelectMenuFont
    .file-select.menu.fileop.m add command -label "Delete" \
    	-command FileSelectDelete
    .file-select.menu.fileop.m add command -label "Rename" \
    	-command FileSelectRename
    .file-select.menu.fileop.m add command -label "Make Directory" \
    	-command FileSelectMakeDir
    .file-select.menu.fileop.m add command -label "Remove Directory" \
    	-command FileSelectRmFir
    pack .file-select.menu.go .file-select.menu.fileop -side left

    # directory entry frame
    frame .file-select.f1 -bd 8
    pack .file-select.f1 -after .file-select.menu
    label .file-select.labeldir -text "Directory:" \
          -font $fileSelectMenuFont
    entry .file-select.dirname -width 40 -relief sunken -bd 2 \
          -textvariable FileSelectDirName \
    	  -font $fileSelectListFont
    pack .file-select.labeldir .file-select.dirname \
    	 -side left -anchor w -in .file-select.f1 -fill x

    # file entry frame
    frame .file-select.f2 -bd 8
    pack .file-select.f2 -side bottom
    label .file-select.labelfile -text "File:" \
    	-font $fileSelectMenuFont
    entry .file-select.filename -width 40 -relief sunken -bd 2 \
         -textvariable FileSelectFileName \
    	-font $fileSelectListFont
    pack  .file-select.labelfile .file-select.filename \
    	-side left -anchor w -in .file-select.f2 -fill x

    # show pattern, "OK" & "CANCEL" buttons
    frame .file-select.f3
    pack .file-select.f3 -side bottom -before .file-select.f2
    label .file-select.lpatt -text "show:" \
    	-font $fileSelectMenuFont
    entry .file-select.pattern -width 10  -relief sunken -bd 2 \
          -textvariable FileSelectPattern \
    	  -font $fileSelectListFont
    button .file-select.ok -text "OK" -command FileSelectAcceptSelection \
    	-font -*-helvetica-bold-r-normal--12-120-*
    button .file-select.cancel -text "Cancel" -command FileSelectCancelSelection \
    	-font -*-helvetica-bold-r-normal--12-120-*
    pack .file-select.lpatt .file-select.pattern .file-select.ok \
         .file-select.cancel -side left -in .file-select.f3 -padx 3m -pady 2m

    # directory list
    frame .file-select.f4 -bd 8
    pack .file-select.f4 -side left -expand 1 -fill both 
    frame .file-select.f4-1 -bd 4 -relief groove
    pack .file-select.f4-1 -expand 1 -fill x -side top -in .file-select.f4
    label .file-select.dirlistlabel -text "Directories" \
    	  -bg $fileSelectBack -fg $fileSelectFore \
    	  -font $fileSelectTitleFont
    pack .file-select.dirlistlabel -fill x -in .file-select.f4-1
    frame .file-select.f4-2
    pack .file-select.f4-2 -after .file-select.f4-1 -in .file-select.f4
    listbox .file-select.dirs -relief sunken -borderwidth 2 \
	    -yscrollcommand ".file-select.scrolldir set" \
            -setgrid 1 \
    	    -font $fileSelectListFont

    pack .file-select.dirs -side left -in .file-select.f4-2 
    scrollbar .file-select.scrolldir -command ".file-select.dirs yview" \
    	-relief ridge
    pack .file-select.scrolldir -side right -after .file-select.dirs \
    	-in .file-select.f4-2 -fill y
    # file list
    frame .file-select.f5 -bd 8
    pack .file-select.f5  -side right -expand 1 -fill both
    frame .file-select.f5-1 -bd 4 -relief groove
    pack .file-select.f5-1 -side top -expand 1 -fill x -in .file-select.f5
    label .file-select.filelistlabel -text "Files" \
    	-bg $fileSelectBack -fg $fileSelectFore \
    	-font $fileSelectTitleFont
    pack .file-select.filelistlabel -fill x -in .file-select.f5-1
    frame .file-select.f5-2
    pack .file-select.f5-2 -after .file-select.f5-1 -in .file-select.f5
    listbox .file-select.files -relief sunken -borderwidth 2 \
    	    -yscrollcommand ".file-select.scrollfile set" \
            -setgrid 1 \
    	    -font $fileSelectListFont
    pack .file-select.files -side left -in .file-select.f5-2
    scrollbar .file-select.scrollfile -command ".file-select.files yview" \
    	-relief ridge
    pack .file-select.scrollfile -side right -before .file-select.files \
    	-in .file-select.f5-2 -fill y

    #
    bind .file-select.filename <Return> FileSelectAcceptSelection
    bind .file-select.dirname <Return> {FileSelectcdto $FileSelectDirName}
    bind .file-select.files <Double-Button-1> {
        FileSelectAcceptSelection
        }
    bind .file-select.pattern <Return> FileSelectShowDir
    bind .file-select.dirs <Double-Button-1> {
    	FileSelectDirSelection
    	}
    chaos:dialogue .file-select 1
    } else {
    selection clear .file-select.files
    selection clear .file-select.dirs
   }

}

#-------------------------------------------------------------------------------
# Show list of directories and files
#-------------------------------------------------------------------------------
proc FileSelectShowDir {} {
    global FileSelectPattern
    .file-select.dirs delete 0 end
    .file-select.files delete 0 end
    .file-select.dirs insert end ".."
    if {[catch {set allfiles [glob *]}]} {return}
    foreach i [lsort $allfiles] {
      if { [file isdirectory $i] } {
        .file-select.dirs insert end $i
      } elseif {[string match $FileSelectPattern $i]} {
        .file-select.files insert end $i
      }
    }
}

#-------------------------------------------------------------------------------
# Select file
#-------------------------------------------------------------------------------
proc FileSelectAcceptSelection {} {
    global FileSelectDirName FileSelectFileName FileSelectResult FileSelectStat
    global FileSelectAllowNonexist

    set dir ${FileSelectDirName}/
    set f $FileSelectFileName
    set FileSelectResult ${dir}${FileSelectFileName}

    if {[file isdirectory ${FileSelectResult}]} {
    	set FileSelectFileName ""
    	FileSelectcdto ${FileSelectResult}
        return
    }
    if {$FileSelectAllowNonexist != 0} {
    	set FileSelectStat 1
        return
    }
    if {! [file exists ${FileSelectResult}]} {
       chaos:alert -title "No such file" \
                   -text [concat "No such file:" $FileSelectResult]
    } else {
      set FileSelectStat 1
    }
    set FileSelectFileName ""
 }

#-------------------------------------------------------------------------------
# Cancel file selection
#-------------------------------------------------------------------------------
proc FileSelectCancelSelection { } {
    global FileSelectResult FileSelectStat
    set FileSelectResult ""
    set FileSelectStat 1
    # return $FileSelectResult
}

#-------------------------------------------------------------------------------
# Get file name from file names list box
#-------------------------------------------------------------------------------
proc FileSelectFileSelection {} {
    global FileSelectFileName
    if {! [chaos:no_selection]} {
       set FileSelectFileName [selection get]
    }
}

#-------------------------------------------------------------------------------
# Get directory name from directory name list box
#-------------------------------------------------------------------------------
proc FileSelectDirSelection {} {
  global FileSelectDirName
  if {! [chaos:no_selection]} {    
     set f [selection get]
     cd $f
     set FileSelectDirName [pwd]
     FileSelectShowDir
  }
}

#-------------------------------------------------------------------------------
# Change directory
#-------------------------------------------------------------------------------
proc FileSelectcdto dir { 
  global FileSelectDirName FileSelectFileName FileSelectStat

  if { ! [ file exists $dir ] } {
     chaos:alert -title "No such directory" \
                 -text [concat {No such directory:} $dir]
     return
    }
  if { [ file isdirectory $dir ] } {
        cd $dir
        set FileSelectDirname [pwd]
        FileSelectShowDir
     } else {
       set FileSelectFileName $dir
       set FileSelectResult $dir
       set FileSelectStat 1
    }
}

#-------------------------------------------------------------------------------
# Remove Directory 
#-------------------------------------------------------------------------------
proc FileSelectRmDir { } {
   global FileSelectDirName FileSelectFileName
   
   set s "exec rmdir $FileSelectDirName"
   FileSelectcdto ".."
   eval $s
   FileSelectShowDir
}

proc FileSelectDelete { } {
   global FileSelectFileName
   
   set s "exec rm $FileSelectFileName"
   set FileSelectFileName ""
   eval $s
   FileSelectShowDir
}

#-------------------------------------------------------------------------------
# RenameFile
#-------------------------------------------------------------------------------
proc FileSelectRename { } {
   global FileSelectFileName FileSelectOldName
   
   set FileSelectOldName $FileSelectFileName
   set FileSelectFileName ""
   focus .file-select.filename
   bind .file-select.filename <Return> FileSelectDoRename
}

proc FileSelectDoRename { } {
   global FileSelectFileName FileSelectOldName
   
   set s "exec mv $FileSelectOldName $FileSelectFileName"
   set FileSelectFileName ""
   eval $s
   bind .file-select.filename <Return> FileSelectAcceptSelection
   FileSelectShowDir
}

#-------------------------------------------------------------------------------
# Make Directory
#-------------------------------------------------------------------------------
proc FileSelectMakeDir { } {
   global FileSelectFileName
   
   set FileSelectFileName ""
   focus .file-select.filename
   bind .file-select.filename <Return> FileSelectDoMakeDir
}

proc FileSelectDoMakeDir { } {
   global FileSelectFileName
   
   set s "exec mkdir $FileSelectFileName"
   set FileSelectFileName ""
   eval $s
   bind .file-select.filename <Return> FileSelectAcceptSelection
   FileSelectShowDir
}

## initialization at load time
set FileSelectDirName ""
set FileSelectFileName ""
set FileSelectAllowNonexist 0
set FileSelectPattern "*"
set FileSelectStat 0
set FileSelectDoExecute ""

proc chaos:edit-file { file } {
    global env

    if [info exists env(EDITOR)] {
       eval exec $env(EDITOR) $file &
    } else {
      exec xedit $file &
    }
}

#-------------------------------------------------------------------------------
# Shows simple file selection box, returns the selected file name as string
#-------------------------------------------------------------------------------
proc FileSelectGetFile {allownonexist} {
    global FileSelectPattern FileSelectDoExecute FileSelectDirName
    global FileSelectStat FileSelectResult FileSelectFileName
    global FileSelectAllowNonexist

    set FileSelectAllowNonexist $allownonexist
    set FileSelectDoExecute ""
    set FileSelectStat 0
    set FileSelectFileName ""

    if { $FileSelectDirName == "" } {
        set FileSelectDirName [pwd]        
    }

    MakeFileSelectPanel
    wm deiconify .file-select

    raise .file-select

    FileSelectShowDir

    focus .file-select.filename

    while { $FileSelectStat == 0 } {
       after 50
       update
       set w [selection own]
       switch $w {
          .file-select.dirs {FileSelectDirSelection; selection clear .file-select.dirs}
          .file-select.files {FileSelectFileSelection; selection clear .file-select.files}
       }
    }
    wm withdraw .file-select
    return $FileSelectResult
}

#===============================================================================
# module list
#===============================================================================

proc chaos:MakeModuleListPanel {args} {
  global fileSelectBack fileSelectFore
  global fileSelectMenuTitleFont fileSelectMenuFont
  global fileSelectTitleFont fileSelectEntryFont fileSelectListFont

  chaos:parse_args {
    {title "Module List"}
    {iconname "Module:List"}
    {id ""}
    {width 20}
    {hight 10}
    {message "List of all modules"}
  }
  if { ! [ winfo exists $id] } {
    # toplevel window
    toplevel $id
    wm title $id $title
    wm iconname $id $iconname
    
    message $id.msg -width 260 -anchor w -text $message \
           -font -*-helvetica-bold-r-normal--12-*
    pack $id.msg -side top -fill both -expand yes -padx 4

    # module list frame
    frame $id.system -bd 4
    pack $id.system -side left -after $id.msg -expand 1 -fill both 
    # title label frame
    #frame $id.system-1 -bd 4 -relief groove
    #pack $id.system-1 -expand 1 -fill x -side top -in $id.system
    #label $id.label -text $title \
    #	  -bg $fileSelectBack -fg $fileSelectFore \
    #	  -font $fileSelectTitleFont
    #pack $id.label -fill x -in $id.system-1
    # module list frame & scroll bar
    frame $id.system-2
    #pack $id.system-2 -after $id.system-1 -in $id.system
    pack $id.system-2 -after $id.msg -in $id.system
    listbox $id.modules -relief sunken -borderwidth 2 \
	    -yscrollcommand "$id.scrolldir set" \
            -setgrid 1 \
            -width $width \
	    -height $height \
    	    -font $fileSelectListFont
    pack $id.modules -side left -in $id.system-2 
    scrollbar $id.scrolldir -command "$id.modules yview" \
    	-relief ridge
    pack $id.scrolldir -side right -after $id.modules \
    	-in $id.system-2 -fill y
    # buttons
    set barid \
        [ chaos:buttonbar $id.b -default update \
          -font -*-helvetica-bold-r-normal--12-* \
          -buttons [format {{update Update} {hide Hide {destroy %s}}} $id] ]
    pack $id.b -side bottom -fill x -after $id.system-2
    }
  #
  selection clear $id.modules
  $id.modules delete 0 end
  wm deiconify $id
  return $barid.update
}

#===============================================================================
# Chaos standard text window
#===============================================================================

proc chaos:make-text-window { args } {
   chaos:parse_args {
     {parent ""}
     {entryname "None"}
     {showtitle 0}
     {width 60}
     {relief groove}
     {font -*-new*-medium-r-normal--14-100-*}
     {background grey}
     {frameback grey}
     {height 12}
   }

   set frame $parent.[string tolower $entryname]
   if {$showtitle} {
    	set body $parent.body
   } else {
        set body $frame
   }
   set text $body.text
   set scroll $body.scroll
    
   if {![winfo exists $frame]} {
      frame $frame -bd 4 -background $frameback
   }
   if {$showtitle} {
      if {![winfo exists $body]} {
         frame $body -background $frameback
      }
   }
   if {![winfo exists $scroll]} {
      scrollbar $scroll -relief flat -command "$text yview"
   }

   if {![winfo exists $body.text]} {
         text $text -relief $relief -bd 4 -yscrollcommand "$scroll set" \
              -font $font \
              -background $background \
              -width $width -height $height
   }
   if {$showtitle} {
      set title [chaos:make-text-title $frame $entryname $frameback]
      pack $title -side top -expand 1 -fill x -in $frame
   } else {
      set title ""
   }
   pack $scroll -side right -fill y
   pack $text -expand yes -side top -fill both
   $text tag configure underline -underline on
   $text tag configure bold -font -*-new*-bold-r-normal--14-*
   $text tag configure bgstipple -background black -borderwidth 0 -bgstipple gray25
   $text tag configure keyword -font -*-helvetica-bold-r-normal--18-*
   $text tag configure fgstipple -fgstipple "gray50"

   
   if {[winfo depth .] > 1} {
       $text tag configure title -background #eed5b7
       $text tag configure raised -background #eed5b7 \
	     -relief raised -borderwidth 2
       # was -backgrount 
       $text tag configure sunken -background #eed5b7 \
	     -relief sunken -borderwidth 2
       $text tag configure groove -background #eed5b7 \
	     -relief groove -borderwidth 2
       $text tag configure search -background SeaGreen4 \
	     -foreground white
    } else {
       $text tag configure title -background black -foreground white
       $text tag configure raised -background white -relief raised -borderwidth 2
       $text tag configure sunken -background white -relief sunken -borderwidth 2
       $text tag configure groove -background white -relief groove -borderwidth 2
       $text tag configure search -background black -forground white
    }

   if {$showtitle} {
	pack $body -expand yes -side top -after $title -fill both -in $frame
   }
   # pack $frame -expand yes -fill both
   return [list $frame $text $scroll $title]
}

proc chaos:make-text-title { parent entryname frameback} {
  set frame $parent.title
  set label $parent.label

  if {![winfo exists $frame]} {
     frame $frame -background $frameback
     label $label -text $entryname -background gray -relief groove -borderwidth 4 \
           -font -*-courier-bold-r-normal-*-120-*
  }
  pack $label -side left -anchor nw -in $frame
  return $frame
}


global chaosSearchString
set chaosSearchString ""

proc chaos:searchMarkTargets {targets} {
  global chaosSearchString
  foreach target $targets {
    chaos:TextSearchMark $target $chaosSearchString search
  }
}

proc chaos:make-find-panel { parent targets } {
  global chaosSearchString
  set frame $parent.findpanel
  set button $parent.findbutton
  set entry $parent.findentry
  if {![winfo exists $frame]} {
    frame $frame
    entry $entry -width 30 -relief sunken -borderwidth 2 \
           -textvariable chaosSearchString \
           -font -*-helvetica-medium-r-normal--12-*
    bind $entry <Return> "chaos:searchMarkTargets {$targets}"
    button $button -text Search -command \
            "chaos:searchMarkTargets {$targets}" \
            -font -*-helvetica-bold-r-normal--12-*
    }
  pack $entry -side right -in $frame
  pack $button -side right -in $frame
  return $frame
}
         
proc chaos:TextSearchMark { w string tag { deletePrev 1 }} {
    if {$deletePrev} {
    	$w tag remove $tag 0.0 end
    }
    if {$string == ""} {return}
    scan [$w index end] %d numLines
    set l [string length $string]
    for {set i 1} {$i <= $numLines} {incr i} {
	if {[string first $string [$w get $i.0 $i.1000]] == -1} {
	    continue
	}
	set line [$w get $i.0 $i.1000]
	set offset 0
	while 1 {
	    set index [string first $string $line]
	    if {$index < 0} {
		break
	    }
	    incr offset $index
	    $w tag add $tag $i.[expr $offset] $i.[expr $offset+$l]
	    incr offset $l
	    set line [string range $line [expr $index+$l] 1000]
	}
    }
}

proc chaos:TerpriWindow {w n} {
  for {set i 0} {$i < $n} {incr i} {
    $w insert end "\n"
  }
}

#===============================================================================
# Text manipulation commands
#===============================================================================

# chaos:text:insert w text -
#   insert text into w at insert point
#   * detects if tags are being used and uses chaos:tag:insert_string 
#   * handles deletion of selection if needed
#-------------------------------------------------------------------------------

proc chaos:text:insert_string { w text } {

  global chaos_text
  global chaos_tag
  
  # all insertions replace selection:
  if [chaos:text:insert_touches_selection $w] {	;# else might be off-screen!
      chaos:text:delete $w sel.first sel.last
  }  
  # if we're using tagged-insertion...
  if [info exists chaos_tag(tags,$w)] {		;# using tagged text
    chaos:tag:insert_string $w $text
  } else {
    set start [$w index insert]			;# ????? USED ?????
    $w insert insert $text
    $w yview -pickplace insert
  }
  set chaos_text(dirty,$w) 1
}

# chaos:text:move w index -
#   move insert mark in w to index
#-------------------------------------------------------------------------------

proc chaos:text:move { w index } {
  $w mark set insert $index
  $w yview -pickplace insert
}

# chaos:text:delete w from to -
#   delete from index from to index to in w
#-------------------------------------------------------------------------------

proc chaos:text:delete { w from to } {
  chaos:text:move $w $from
  $w delete $from $to
  set chaos_text(dirty,$w) 1
}

# chaos:text:replace w from to string -
#   replace range with string, preserving tags at from
#-------------------------------------------------------------------------------

proc chaos:text:replace { w from to string } {
  set start [$w index $from]
  set tags [$w tag names $from]
  
  $w mark set insert $from
  $w delete insert $to
  $w insert insert $string
  
  foreach tag [$w tag names $start] {
    $w tag remove $tag $start insert
  }
  foreach tag $tags {
    $w tag add $tag $start insert
  }
  set chaos_text(dirty,$w) 1
}


# chaos:text:mark_dirty w - mark widget w as dirty (modified)
#-------------------------------------------------------------------------------

proc chaos:text:mark_dirty { w } {
  global chaos_text
  set chaos_text(dirty,$w) 1
}

# chaos:text:mark_clean w - mark widget w as clean (unmodified)
#-------------------------------------------------------------------------------

proc chaos:text:mark_clean { w } {
  global chaos_text
  set chaos_text(dirty,$w) 0
}


# chaos:text:is_dirty w -
#   return 1 if w is dirty (modified) else 0
#   (returns 1 if w hasn't been set dirty or clean)
#-------------------------------------------------------------------------------

proc chaos:text:is_dirty { w } {
  global chaos_text
  if [info exists chaos_text(dirty,$w)] {
    return $chaos_text(dirty,$w)
  } else {
    return 1
  }
}

# chaos:text:has_selection t -
#   return true if selection made in t, else false
#-------------------------------------------------------------------------------

proc chaos:text:has_selection { t } {
  set selrange [$t tag nextrange sel 1.0]
  
  if {"x$selrange" == "x"} {                    ;# returns {} if none
    return 0
  } else {
    return 1
  }
}

# chaos:text:insert_touches_selection t -
#   return true if selection exists in t and insert is inside or next
#   to it (as will be the case if you just made the selection with
#   the mouse)
#-------------------------------------------------------------------------------

proc chaos:text:insert_touches_selection { t } {
  if {! [chaos:text:has_selection $t]} {		;# no selection
    return 0
  }
  if [$t compare insert < sel.first] {		;# insert before selection
    return 0
  }
  if [$t compare insert > sel.last] {		;# insert after selection
    return 0
  }
  return 1
}

#===============================================================================
# Tag
#===============================================================================
# jtexttags.tcl - tagged typing and tagging the selection for Text bindings
#
# Copyright 1992-1994 by Jay Sekora	.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 
# for non­profit, noncommercial use.

# TO DO: clear_tags, clear_marks

# see also chaos:text:insert_string in jtext.tcl

#
# tags used by these functions are of the form $category:$attribute:$value,
# where you can always say "$w tag configure -$attribute $value".
# two potential tags conflict if their $attribute is the same.
#

######################################################################
# insert text into w at insert,
#   possibly honouring current tag list for widget
#   partly lifted from insertWithTags in mkStyles.tcl demo
#   used by jtext.tcl if a tag list is specified
######################################################################

proc chaos:tag:insert_string { w text } {
  global chaos_tag
  
  if {! [info exists chaos_tag(tags,$w)]} {
    set chaos_tag(tags,$w) {}
  }
  
  set start [$w index insert]
  $w insert insert $text
  $w yview -pickplace insert
  #
  # apply styles from tag list
  foreach tag [$w tag names $start] {
    $w tag remove $tag $start insert
  }
  foreach i $chaos_tag(tags,$w) {
    $w tag add $i $start insert
  }
}

######################################################################
# set tags to use when inserting typed text
#   if $tags is the empty list, inserted text will be plain.
######################################################################

proc chaos:tag:set_tags { w args } {
  global chaos_tag
  
  set chaos_tag(tags,$w) $args
  
  # now configure any display tags in $args to display properly:
  
  foreach tag $args {
    set split_tag [split $tag ":"]
    set category [lindex $split_tag 0]		;# e.g. display, command
    if {"x$category" == "xdisplay"} {
      set attribute [lindex $split_tag 1]	;# e.g. foreground, font
      set value [lindex $split_tag 2]		;# e.g. blue, 12x24
      
      catch {
        $w tag configure $tag -$attribute $value
      }
      $w tag lower $tag				;# so sel e.g. overrides
    }
  }

}

######################################################################
# clear tag list for inserting typed text; 
#   when used with jtext.tcl, restores normal Tk behaviour of 
#   inheriting tag from surrounding text
######################################################################

proc chaos:tag:clear_tags { w } {
  global chaos_tag
  
  catch {
    unset chaos_tag(tags,$w)
  }
}

######################################################################
# chaos:tag:set_tag w tag -
#   add a tag to list, overriding any conflicting tag
######################################################################

proc chaos:tag:set_tag { w tag } {
  global chaos_tag
  
  set split_tag [split $tag ":"]
  set category [lindex $split_tag 0]		;# e.g. display, command
  set attribute [lindex $split_tag 1]		;# e.g. foreground, font
  set value [lindex $split_tag 2]		;# e.g. blue, 12x24
  
  if {"x$category" == "xdisplay"} {
    catch {
      $w tag configure $tag -$attribute $value
    }
    $w tag lower $tag				;# so sel e.g. overrides
  }
  
  if {! [info exists chaos_tag(tags,$w)]} {		;# make sure list exists
    set chaos_tag(tags,$w) $tag
    return
  }
  
  set new_tags $tag				;# start with tag argument,
  
  foreach old_tag $chaos_tag(tags,$w) {		;# append compatible old tags
    set old_split_tag [split $old_tag ":"]
    set old_category [lindex $old_split_tag 0]
    set old_attribute [lindex $old_split_tag 1]
    if {"$category:$attribute" != "$old_category:$old_attribute"} {
      lappend new_tags $old_tag
    }
  }
  
  set chaos_tag(tags,$w) $new_tags
  
  return
}


######################################################################
# chaos:tag:clear_tag w pattern -
#   remove tags matching pattern from list
######################################################################

proc chaos:tag:clear_tag { w pattern } {
  global chaos_tag
  
  if {! [info exists chaos_tag(tags,$w)]} {		;# make sure list exists
    return
  }
  
  set new_tags {}				;# start with empty list
  
  foreach old_tag $chaos_tag(tags,$w) {		;# append old tags unless match
    if {! [string match $pattern $old_tag]} {
      lappend new_tags $old_tag
    }
  }
  
  set chaos_tag(tags,$w) $new_tags
  
  return
}

######################################################################
# chaos:tag:tag_text w tag first last -
#   apply tag to text, overriding any conflicting tag
######################################################################

proc chaos:tag:tag_text { w tag first last } {
  if [$w compare $first > $last] {
    error "Text index \"first\" > \"last\" in chaos:tag:tag_text."
  }
  
  set split_tag [split $tag ":"]
  set category [lindex $split_tag 0]		;# e.g. display, command
  set attribute [lindex $split_tag 1]		;# e.g. foreground, font
  set value [lindex $split_tag 2]		;# e.g. blue, 12x24
  
  foreach possible_tag [$w tag names] {
    set split_old [split $possible_tag ":"]
    set old_category [lindex $split_old 0]
    set old_attribute [lindex $split_old 1]
    
    if {"$old_category:$old_attribute" == "$category:$attribute"} {
      $w tag remove $possible_tag $first $last
    }
  }
  
  $w tag add $tag $first $last
  
  if {"x$category" == "xdisplay"} {
    $w tag configure $tag -$attribute $value	;# should be catch'ed
    $w tag lower $tag				;# so sel e.g. overrides
  }
}


######################################################################
# chaos:tag:untag_text w pattern first last -
#   remove tags matching pattern from text between first and last in w
######################################################################

proc chaos:tag:untag_text { w pattern first last } {
  if [$w compare $first > $last] {
    error "Text index \"first\" > \"last\" in chaos:tag:tag_text."
  }
  
  foreach possible_tag [$w tag names] {
    if [string match $pattern $possible_tag] {
      $w tag remove $possible_tag $first $last
    }
  }
}

######################################################################
# configure all current display tags in widget w
######################################################################

proc chaos:tag:configure_display_tags { w } {
  foreach tag [$w tag names] {
    set split_tag [split $tag ":"]
    set category [lindex $split_tag 0]		;# e.g. display, command
    if {"x$category" == "xdisplay"} {
      set attribute [lindex $split_tag 1]	;# e.g. foreground, font
      set value [lindex $split_tag 2]		;# e.g. blue, 12x24
      
      catch {
        $w tag configure $tag -$attribute $value
      }
      $w tag lower $tag				;# so sel e.g. overrides
    }
  }
}

######################################################################
# return non-text content (tags and marks) of a text widget
######################################################################

proc chaos:tag:get_annotation {t} {
  set tags {}
  set marks {}
  foreach tag [$t tag names] {
    set ranges [$t tag ranges $tag]
    if {"x$ranges" != "x"} {
      lappend tags [list $tag $ranges]
    }
  }
  foreach mark [$t mark names] {
    lappend marks [list $mark [$t index $mark]]
  }
  return [list $tags $marks]
  close $file
}

######################################################################
# set non-text content (tags and marks) of a text widget
### DOCUMENT "state"
######################################################################

proc chaos:tag:set_annotation { {t} {state} } {
  set tags [lindex $state 0]
  set marks [lindex $state 1]
  foreach pair $marks {
    $t mark set [lindex $pair 0] [lindex $pair 1]
  }
  foreach pair $tags {
    set tag [lindex $pair 0]
    set ranges [lindex $pair 1]
    set length [llength $ranges]
    for {set i 0; set i1 1} {$i1 < $length} {incr i 2; incr i1 2} {
      $t tag add $tag [lindex $ranges $i] [lindex $ranges $i1]
    }
  }
  chaos:tag:configure_display_tags $t	;# make sure things look right
  $t yview -pickplace insert
}

######################################################################
# archive text widget to file, including state
######################################################################

proc chaos:tag:archive_text_widget { {t} {filename} } {
  set text [$t get 1.0 end]
  set state [chaos:tag:get_annotation $t]
  
  chaos:fileio:write $filename [list $text $state]
}

######################################################################
# read entire contents of text widget from file, including state
######################################################################

proc chaos:tag:restore_text_widget { {t} {filename} } {
  set archive [chaos:fileio:read $filename]
  
  set text [lindex $archive 0]
  set state [lindex $archive 1]
  
  set state_option \
    [lindex [$t configure -state] 4]		;# in case it's disabled
  $t configure -state normal			;# make sure we can change
  
  $t delete 1.0 end
  $t insert end $text
  chaos:tag:set_annotation $t $state
  
  $t configure -state $state_option		;# might have been disabled
}

######################################################################
# apply "state" to text starting at a given offset
#   this is used for inserting tagged text into a text widget
#   someplace other than the beginning.  by default, ignores "sel" tag
#   and "insert" and "current" marks.  DOESN'T YET WORK!
######################################################################

proc chaos:tag:apply_annotation { args } {
  chaos:parse_args {
    {offset 1.0}
    {ignoretags {sel}}
    {ignoremarks {insert current}}
  }
  
  if {[llength $args] < 2} {
    error \
      "wrong # args: should be chaos:tag:apply_annotation ?options? widget state"
  }
  
  set widget [lindex $args 0]
  set state [lindex $args 1]
  
  set tags [lindex $state 0]
  set marks [lindex $state 1]
  
  foreach pair $marks {
    set mark [lindex $pair 0]
    set index [lindex $pair 1]
    if {[lsearch $ignoremarks $mark] != -1} {
      $widget mark set $mark [chaos:tag:offset_index $index $offset]
    }
  }
  foreach pair $tags {
    set tag [lindex $pair 0]
    set ranges [lindex $pair 1]
    set length [llength $ranges]
    for {set i 0; set i1 1} {$i1 < $length} {incr i 2; incr i1 2} {
      if {[lsearch $ignoretags $tag] != -1} {
        set from [chaos:tag:offset_index [lindex $ranges $i] $offset]
        set to [chaos:tag:offset_index [lindex $ranges $i1] $offset]
        
        $widget tag add $tag $from $to
      }
    }
  }
  chaos:tag:configure_display_tags $widget	;# make sure things look right
}

######################################################################
# offset a text index by a given amount
#   the line offset is always added, but the character offset is only
#   changed on the first line
######################################################################

proc chaos:tag:offset_index { index offset } {
  set offset_split [split $offset "."]
  set line_offset [expr [lindex $offset_split 0] - 1]
  
  if [string match "1.*" $index] {
    # first line - need to offset both line and character
    set char_offset [lindex $offset_split 1]
    set index_split [split $index "."]
    set index_line [lindex $index_split 0]
    set index_char [lindex $index_split 1]
    return [expr $index_line + $line_offset].[expr $index_char + $char_offset]
  } else {
    # subsequent line - only need to offset the line number
    # can pretend it's real arithmetic
    return [expr $index + $line_offset]
  }
}

#===============================================================================
# Rich Text
#===============================================================================
# jrichtext.tcl - procedures for dealing with rich text
# 
# Copyright 1992-1994 by Jay Sekora.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 
# for non­profit, noncommercial use.
######################################################################

# CHANGES:
#   dual usage; chaos:rt:textfonts with a text widget vs. full rich-text

# chaos:tagged_insert w text args - insert tagged text into a text widget
# chaos:rt text dest - prepare to write rich text to text widget dest
# chaos:rt:type - return type of current rich text destination (text, TeX)
# chaos:rt:destination - return current rich text destination (widget, file)
# chaos:rt:textfonts {style font}... - set fonts for text widget
# chaos:rt:done - finish writing rich text (clear vars, close files)
# chaos:rt:rm text - write rich text (roman)
# chaos:rt:it text - write rich text (italic)
# chaos:rt:bf text - write rich text (bold face)
# chaos:rt:bi text - write rich text (bisexual)
# chaos:rt:tt text - write rich text (typewriter - monospaced)
# chaos:rt:hl text - write rich text (`headline' - larger bold)
# chaos:rt:tab - tab in rich text
# chaos:rt:cr - line break in rich text
# chaos:rt:par - paragraph break in rich text
# chaos:rt:mkabbrevs - make shorter convenience procs, for text-intensive apps
# rm - dummy do-nothing procedure to prevent unknown from calling /bin/rm
#   if you forget to chaos:rt:mkabbrevs

######################################################################
# chaos:tagged_insert - append to a text widget with a particular tag
#   (lifted from mkStyles.tcl demo, where it was insertWithTags)
######################################################################

# The procedure below inserts text into a given text widget and
# applies one or more tags to that text.  The arguments are:
#
# w		Window in which to insert
# text		Text to insert (it's inserted at the "insert" mark)
# args		One or more tags to apply to text.  If this is empty
#		then all tags are removed from the text.

proc chaos:tagged_insert {w text args} {
  set start [$w index insert]
  $w insert insert $text
  foreach tag [$w tag names $start] {
    $w tag remove $tag $start insert
  }
  foreach i $args {
    $w tag add $i $start insert
  }
}

######################################################################
# chaos:rt text dest - prepare to write rich text to text widget dest
#   future versions will support PostScript, TeX, maybe canvas, etc.
######################################################################

proc chaos:rt { {type {}} {destination stdout} } {
  global chaos_rt
  
  case $type in {
    {text} {			;# output to a text widget
      set chaos_rt(type) $type
      set chaos_rt(destination) $destination
      $chaos_rt(destination) delete 0.0 end
      $chaos_rt(destination) configure -wrap word
      catch {
        $chaos_rt(destination) configure -font \
          -adobe-helvetica-medium-r-normal--*-120-*
        $chaos_rt(destination) tag configure richtext:font:roman -font \
          -adobe-helvetica-medium-r-normal--*-120-*
        $chaos_rt(destination) tag configure richtext:font:italic -font \
          -adobe-helvetica-medium-o-normal--*-120-*
        $chaos_rt(destination) tag configure richtext:font:bold -font \
          -adobe-helvetica-bold-r-normal--*-120-*
        $chaos_rt(destination) tag configure richtext:font:bolditalic -font \
          -adobe-helvetica-bold-o-normal--*-120-*
        $chaos_rt(destination) tag configure richtext:font:typewriter -font \
          -adobe-courier-medium-r-normal--*-120-*
        $chaos_rt(destination) tag configure richtext:font:heading0 -font \
          -adobe-helvetica-bold-o-normal--*-240-*
        $chaos_rt(destination) tag configure richtext:font:heading1 -font \
          -adobe-helvetica-bold-o-normal--*-180-*
        $chaos_rt(destination) tag configure richtext:font:heading2 -font \
          -adobe-helvetica-bold-o-normal--*-140-*
        $chaos_rt(destination) tag configure richtext:font:heading3 -font \
          -adobe-helvetica-bold-o-normal--*-120-*
        $chaos_rt(destination) tag configure richtext:font:heading4 -font \
          -adobe-helvetica-bold-o-normal--*-100-*
        $chaos_rt(destination) tag configure richtext:font:heading5 -font \
          -adobe-helvetica-bold-o-normal--*-80-*
      }
    }
    default {
      tkerror "chaos:rt $type $destination: only type \"text\" is supported."
    }
  }
}

######################################################################
# chaos:rt:textfonts w {{style fontlist}...} - set fonts for text widget w
#   style is one of {roman italic bold bolditalic typewriter} or
#   {heading0, ..., heading5}; font is list of X fonts, in order of
#   decreasing preference (cf chaos:configure_tag_font in jtkutils.tcl).
######################################################################

proc chaos:rt:textfonts { w list } {
  foreach pair $list {
    set tag "richtext:font:[lindex $pair 0]"
    set fontlist [lindex $pair 1]
    chaos:configure_tag_font $w $tag $fontlist
  }
}

######################################################################
# chaos:rt:type - return type of current rich text destination (text, TeX)
######################################################################

proc chaos:rt:type {} {
  global chaos_rt
  
  if { (! [info exists chaos_rt(type)])} {
    # this might be considered an error
    return {}
  } else {
    return $chaos_rt(type)
  }
}

######################################################################
# chaos:rt:destination - return current rich text destination (widget, file)
######################################################################

proc chaos:rt:destination {} {
  global chaos_rt
  
  if { (! [info exists chaos_rt(destination)]) } {
    # this might be considered an error
    return {}
  } else {
    return $chaos_rt(destination)
  }
}

######################################################################
# chaos:rt:done - finish writing rich text (clear vars, close files)
######################################################################

proc chaos:rt:done {} {
  global chaos_rt

  # to start, would close files if appropriate
  
  set chaos_rt(type) {}
  set chaos_rt(destination) {}
}
  
######################################################################
# CREATE PROCEDURES FOR:
# chaos:rt:rm text - write rich text (roman)
# chaos:rt:it text - write rich text (italic)
# chaos:rt:bf text - write rich text (bold face)
# chaos:rt:bi text - write rich text (bisexual)
# chaos:rt:tt text - write rich text (typewriter - monospaced)
# chaos:rt:hl text - write rich text (`headline' - larger bold)
######################################################################

set tmp_body {
  set type [chaos:rt:type]
  
  case $type in {
    {text} {			;# output to a text widget
      chaos:tagged_insert [chaos:rt:destination] $text $tag
    }
    default {
      tkerror "chaos:rt type \"$type\" is not supported."
    }
  }
}

foreach pair {
  {rm roman}
  {it italic}
  {bf bold}
  {bi bolditalic}
  {tt typewriter}
  {hl heading1}
  {h0 heading0}
  {h1 heading1}
  {h2 heading2}
  {h3 heading3}
  {h4 heading4}
  {h5 heading5}
} {
  set command [lindex $pair 0]
  set style [lindex $pair 1]
  proc chaos:rt:$command {text} "  set tag richtext:font:$style\n$tmp_body"
}

######################################################################
# chaos:rt:tab - tab in rich text
######################################################################

proc chaos:rt:tab {} {
  chaos:rt:rm "\t"
}

######################################################################
# chaos:rt:cr - line break in rich text
######################################################################

proc chaos:rt:cr {} {
  chaos:rt:rm "\n"
}

######################################################################
# chaos:rt:par - paragraph break in rich text
######################################################################

proc chaos:rt:par {} {
  chaos:rt:rm "\n\n"
}

######################################################################
# chaos:rt:mkabbrevs - make shorter convenience procs, for text-intensive apps
######################################################################

# this creates shorter aliases rm, it, bf, bi, tt, hl, tab, cr, and
# par identical to the corresponding procedures starting with "chaos:rt:"

proc chaos:rt:mkabbrevs {} {
  foreach proc {rm it bf bi tt hl tab cr par} {
    proc $proc [info args chaos:rt:$proc] [info body chaos:rt:$proc]
  }
}

######################################################################
# rm - dummy do-nothing procedure to prevent unknown from calling /bin/rm
#   if you forget to chaos:rt:mkabbrevs
######################################################################

proc rm {args} {
  tkerror "Called `rm' without calling `chaos:rt:mkabbrevs'."
}
