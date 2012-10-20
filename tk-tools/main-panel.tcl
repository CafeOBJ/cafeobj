# basic initialisation
# only has an effect the first time it's called.
######################################################################

proc chaos-ed:init {} {
  global CHAOS-ED_INITIALISED		;# flag - already called?
  if [info exists CHAOS-ED_INITIALISED] {
    return				;# only initialise once
  }
  global CHAOS-ED_WINDOW_COUNT		;# number of toplevel windows
  set CHAOS-ED_WINDOW_COUNT 0
  
  global UNDOPTR			;# current index into undo ring
  set UNDOPTR 0
  
  global WORD_END
  set WORD_END {
    ampersand
    apostrophe
    asterisk
    braceright
    bracketright
    colon
    comma
    exclam
    minus
    parenright
    period
    question
    quotedbl
    quoteright
    semicolon
    slash
    underscore
  }
  
  global CUTBUFFER
  set CUTBUFFER {}
  global ABBREV				;# last abbrev expanded
  set ABBREV {}
  global ABBREV_POS			;# start of last abbrev
  set ABBREV_POS {}
  global MATCH				;# last match found
  set MATCH {}
  global MATCH_POS			;# position of last match found
  set MATCH_POS {}
  global ABBREV_LIST			;# list of abbrevs read from file
  set ABBREV_LIST {}			;# (not yet used)
  global ABBREVS			;# text-indexed array of expansions

  set CHAOS-ED_INITIALISED 1

}

######################################################################
# edit a file
######################################################################

proc chaos-ed:chaos-ed { args } {
  global CHAOS-ED_WINDOW_COUNT		;# number of toplevel windows
  
  chaos:parse_args {
    {window unspecified}
    {file {}}
  }
  
  chaos-ed:init				;# ignored second etc. time it's called
  
  # pick a window name if the user hasn't supplied one
  if { "x$window" == "xunspecified" } {
    set window [chaos-ed:new_window_name]
  }
  
  if { ! [winfo exists $window] } {
    toplevel $window
  }

  incr CHAOS-ED_WINDOW_COUNT		;# keep count of each window opened
  
  set text [chaos-ed:top_to_text $window]
  
  if {"x$file" != "x"} {
    chaos-ed:set_filename $window $file
  }
  chaos-ed:set_choas_mode $window
  chaos-ed:mkwindow $window
  chaos-ed:apply_mode $window
  
  chaos-ed:mkbindings $text $text
  if {"x$file" != "x"} {
    tkwait visibility $text		;# bug workaround for unpatched tk3.6
    chaos-ed:read $file $text
  }
  return $window			;# for caller to manipulate


######################################################################
# get an unused name for a window
######################################################################

proc chaos-ed:new_window_name {} {
  set i 0
  while {[winfo exists .chaos-ed$i]} {
    incr i
  }
  return .chaos-ed$i
}

######################################################################
# abbrev - set an abbreviation (used by .tk/abbrevs.tcl
######################################################################

proc abbrev {{abbrev} {expansion}} {
  global ABBREVS
  
  set ABBREVS($abbrev) $expansion
}

######################################################################
# regsub in selection in t
#   if the original text ends with a newline, it is removed and
#   replaced at the end.
### SHOULD BE MORE GENERAL (eg entire file)
######################################################################

proc chaos-ed:text_regsub { t regex subst } {
  if { ! [chaos:text:has_selection $t]} {
    chaos:alert -text "No selection made in text."
    return 1
  }
  
  chaos-ed:cmd:save_checkpoint $t			;# save undo information
  
  set finalcr 0
  
  set text [selection get]
  if [regexp -- "\n\$" $text] {
    set text [string trimright $text "\n"]
    set finalcr 1
  }
  
  regsub -all -- $regex $text $subst result
  
  if $finalcr {
    append result "\n"
  }
  
  chaos:text:replace $t sel.first sel.last $result
}

######################################################################
# pipe selection through command (and replace)
#   if original text has a newline and new text doesn't, a newline
#   is appended.  this is a workaround for some filters that drop the
#   newline.  not perfect, but should be adequate.
######################################################################

proc chaos-ed:pipe { t command } {
  if { ! [chaos:text:has_selection $t]} {
    chaos:alert -text "No selection made in text."
    return 1
  }
  
  chaos-ed:cmd:save_checkpoint $t			;# save undo information
  
  set finalcr 0
  
  set text [selection get]
  if [regexp -- "\n\$" $text] {
    set finalcr 1
  }
  
  if { ! $finalcr } {				;# doesn't already have newline
    append text "\n"
  }
  
  if [catch { eval exec $command << [list $text] } result] {
    chaos:alert -text "Error from $command: $result"
    return 1
  }
  
  if {$finalcr && ( ! [regexp -- "\n\$" $result] )} {
    append result "\n"
  }
  
  chaos:text:replace $t sel.first sel.last $result
  
  return 0
}

######################################################################
# return string with first char capitalised
######################################################################

proc chaos-ed:capitalise {string} {
  set cap [format {%s%s} \
    [string toupper [string range $string 0 0]] \
    [string range $string 1 end]]
  return $cap
}

######################################################################
# return string with first char lowercased
######################################################################

proc chaos-ed:uncapitalise {string} {
  set lc [format {%s%s} \
    [string tolower [string range $string 0 0]] \
    [string range $string 1 end]]
  return $lc
}

######################################################################
# go to a particular line
######################################################################

proc chaos-ed:go_to_line { t {lineno 0} } {
  set result [catch {
    chaos:tb:move $t $lineno.0
  }]
  if $result then {chaos:alert -text "`$lineno' is not a valid line number."}
}

######################################################################
# set the filename corresponding to a window.  the window can be
# specified either as a text widget, or as that text widget's
# corresponding toplevel window.
######################################################################

proc chaos-ed:set_filename { w filename } {
  global CHAOS-ED_FILES
  
  if { [winfo class $w] == "Text" } {
    set window [chaos-ed:text_to_top $w]
#    set text $w
  } else {
    set window $w
#    set text [chaos-ed:top_to_text $w]
  }
  
  set CHAOS-ED_FILES($window) $filename
}

######################################################################
# return the filename corresponding to a window.  the window can be
# specified either as a text widget, or as that text widget's
# corresponding toplevel window.  if no filename has been set for that
# window, returns {}.
######################################################################

proc chaos-ed:get_filename { w } {
  global CHAOS-ED_FILES
  
  if { [winfo class $w] == "Text" } {
    set window [chaos-ed:text_to_top $w]
#    set text $w
  } else {
    set window $w
#    set text [chaos-ed:top_to_text $w]
  }
  
  if [info exists CHAOS-ED_FILES($window)] {
    return $CHAOS-ED_FILES($window)
  } else {
    return {}
  }
}

# chaos-ed_bindings.tcl - bindings for command accelerators for chaos-ed
# 
# Copyright 1992-1994 by Jay Sekora.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 
# for non-profit, noncommercial use.

######################################################################
# chaos-ed:mkbindings - set keyboard shortcuts and special map additions
#   widgets and t are often the same, but needn't be - widgets could
#   also include entry widgets
######################################################################

proc chaos-ed:mkbindings {widgets t} {
  global WORD_END
  # the following can't be redefined in ~/.tk/textbindings.tcl;
  # if you want to change them, do so in $HOME/.tk/chaos-edrc.tcl
  #
  foreach w $widgets {
    bind $w <Meta-Tab>		{chaos-ed:cmd:toggle_dabbrev %W}
    bind $w <Meta-space>	{chaos-ed:cmd:toggle_sabbrev %W}
    bind $w <Meta-minus>	{chaos-ed:cmd:hyphen %W}
    bind $w <Meta-semicolon>	{chaos-ed:cmd:dabbrev %W}
    catch {
      bind $w <Meta-quoteright>	{chaos-ed:cmd:sabbrev %W}
    }
    catch {
      bind $w <Meta-apostrophe>	{chaos-ed:cmd:sabbrev %W}
    }
    bind $w <Meta-bar>		{chaos-ed:cmd:run_pipe %W}
    bind $w <Meta-exclam>	{chaos-ed:cmd:run_command %W}
    bind $w <Meta-bracketleft>	"chaos-ed:text_regsub %W {(^|\n)\[> \] } {\\1}"
    bind $w <Meta-bracketright>	"chaos-ed:text_regsub %W {(^|\n)} {\\1  }"
    bind $w <Meta-a>		{chaos-ed:cmd:select_all %W}
    bind $w <Meta-B>		{chaos-ed:font:bold %W}
    bind $w <Meta-c>		{chaos-ed:cmd:copy %W}
    bind $w <Meta-C>		{chaos-ed:cmd:current_line %W}
    bind $w <Meta-f>		{chaos-ed:cmd:find %W}
    bind $w <Meta-F>		"chaos-ed:pipe $t {fmt}"
    bind $w <Meta-g>		{chaos-ed:cmd:find_again %W}
    bind $w <Meta-G>		{chaos:global_pref_panel}
    bind $w <Meta-h>		{chaos-ed:cmd:help %W}
    bind $w <Meta-i>		{chaos-ed:cmd:insfile %W}
    bind $w <Meta-I>		{chaos-ed:font:italic %W}
    bind $w <Meta-l>		{chaos-ed:cmd:load %W}
    bind $w <Meta-L>		{chaos-ed:cmd:go_to_line %W}
    bind $w <Meta-m>		{chaos-ed:cmd:ask_mode  %W}
    bind $w <Meta-Key-M>	{chaos-ed:font:typewriter %W}
    bind $w <Meta-n>		{chaos-ed:cmd:new_window %W}
    bind $w <Meta-N>		{chaos-ed:cmd:note %W}
    bind $w <Meta-p>		{chaos-ed:cmd:print %W}
    bind $w <Meta-P>		{chaos-ed:cmd:edit_prefs %W}
    bind $w <Meta-R>		{chaos-ed:font:roman %W}
    bind $w <Meta-s>		{chaos-ed:cmd:save %W}
    bind $w <Meta-S>		{chaos-ed:cmd:saveas %W}
    bind $w <Meta-T>		{chaos:prompt_tcl}
    bind $w <Meta-U>		{chaos:prompt_unix}
    bind $w <Meta-v>		{chaos-ed:cmd:paste %W}
    bind $w <Meta-V>		{chaos-ed:cmd:xpaste %W}
    bind $w <Meta-x>		{chaos-ed:cmd:cut %W}
    bind $w <Meta-X>		{chaos-ed:font:bolditalic %W}
    bind $w <Meta-q>		{chaos-ed:cmd:quit %W}
    bind $w <Meta-w>		{chaos-ed:cmd:close %W}
    bind $w <Meta-z>		{chaos-ed:cmd:undo %W}
    bind $w <Meta-Z>		{chaos-ed:cmd:redo %W}
 }
  
  # set up bindings for word-end punctuation (for abbrevs):
  
  foreach key $WORD_END {
    foreach map {basic vi-insert emacs-normal edt-normal} {
      chaos:tkb:mkmap $w $map $map [format {
        {%s			chaos-ed:self_insert_punct}
      } $key]
    }
  }
  
  # set up bindings for a few other special characters:
  
  foreach map {basic vi-insert emacs-normal edt-normal} {
    chaos:tkb:mkmap $w $map $map [format {
      {Tab			chaos-ed:tabkey}
    } $key]
    chaos:tkb:mkmap $w $map $map [format {
      {space			chaos-ed:spacebar}
    } $key]
    chaos:tkb:mkmap $w $map $map [format {
      {Return			chaos-ed:returnkey}
    } $key]
  }
  
  # additional application-specific Emacs-style keyboard bindings:
  
  chaos:tkb:mkmap $w emacs-normal emacs-normal {
    {Control-s			chaos-ed:cmd:find_forward}
    {Control-r			chaos-ed:cmd:find_backward}
  }
  chaos:tkb:mkmap $w emacs-escape emacs-normal {
    {percent			chaos-ed:cmd:find}
  }
  chaos:tkb:mkmap $w emacs-control-x emacs-normal {
    {Control-s			chaos-ed:cmd:save}
    {Control-w			chaos-ed:cmd:saveas}
    {Control-f			chaos-ed:cmd:load}
    {Control-v			chaos-ed:cmd:load}
    {Control-c			chaos-ed:cmd:quit}
  }
  
  # additional application-specific vi-style keyboard bindings:
  
  chaos:tkb:mkmap $w vi-command vi-command {
    {slash			chaos-ed:cmd:find_forward}
    {question			chaos-ed:cmd:find_backward}
    {n				chaos-ed:cmd:find_again}
  }
  
  # create a vi-Z map for the "ZZ" command:
  
  chaos:tkb:mkmap $w vi-command vi-command {
    {Z				chaos:tkb:new_mode vi-Z}
  }
  
  chaos:tkb:mkmap $w vi-Z vi-command {
    {DEFAULT			chaos:tb:no_op}
    {Shift-DEFAULT		chaos:tb:no_op}
    {Control-DEFAULT		chaos:tb:no_op}
    {Meta-DEFAULT		chaos:tb:no_op}
    {Z				chaos-ed:cmd:done}
  }
}

# chaos-ed_checkpoint.tcl - undo and redo support for chaos-ed
# 
# Copyright 1992-1994 by Jay Sekora.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 
# for non-profit, noncommercial use.

######################################################################
# save current state in undo ring
#   { t args } lets it be used with chaos:tkb:mkmap
######################################################################

proc chaos-ed:cmd:save_checkpoint { t args } {
  global CKPT_TEXT CKPT_ANNO CHAOS-ED_PREFS UNDOPTR

  if $CHAOS-ED_PREFS(undolevels) {
    set CKPT_TEXT($UNDOPTR) [$t get 1.0 end]
    set CKPT_ANNO($UNDOPTR) [chaos:tag:get_annotation $t]
    incr UNDOPTR
    set old [expr {$UNDOPTR - $CHAOS-ED_PREFS(undolevels)}]
    catch {
      unset CKPT_TEXT($old)			;# forget a previous checkpoint
      unset CKPT_ANNO($old)
    }
  } else {
    chaos:alert -text "You don't have undo turned on."
  }
}

######################################################################
# chaos-ed:cmd:undo - restore from saved state (moving backwards in undo ring)
#   { t args } lets it be used with chaos:tkb:mkmap
######################################################################

proc chaos-ed:cmd:undo { t args } {
  global CKPT_TEXT CKPT_ANNO CHAOS-ED_PREFS UNDOPTR

  if $CHAOS-ED_PREFS(undolevels) {
    set CKPT_TEXT($UNDOPTR) [$t get 1.0 end]
    set CKPT_ANNO($UNDOPTR) [chaos:tag:get_annotation $t]
    incr UNDOPTR -1
    if {![info exists CKPT_TEXT($UNDOPTR)]} {
      incr UNDOPTR
      chaos:alert -text "No more undo information available."
    }
    $t delete 1.0 end
    $t insert end $CKPT_TEXT($UNDOPTR)
    chaos:tag:set_annotation $t $CKPT_ANNO($UNDOPTR)
    $t yview -pickplace insert
  } else {
    chaos:alert -text "You aren't saving any undo information."
  }
}

######################################################################
# restore from saved state (moving forwards in undo ring)
#   { t args } lets it be used with chaos:tkb:mkmap
######################################################################

proc chaos-ed:cmd:redo { t args } {
  global CKPT_TEXT CKPT_ANNO CHAOS-ED_PREFS UNDOPTR

  if $CHAOS-ED_PREFS(undolevels) {
    set CKPT_TEXT($UNDOPTR) [$t get 1.0 end]
    set CKPT_ANNO($UNDOPTR) [chaos:tag:get_annotation $t]
    incr UNDOPTR
    if {![info exists CKPT_TEXT($UNDOPTR)]} {
      incr UNDOPTR -1
      chaos:alert -text "No more redo information available."
    }
    $t delete 1.0 end
    $t insert end $CKPT_TEXT($UNDOPTR)
    chaos:tag:set_annotation $t $CKPT_ANNO($UNDOPTR)
    $t yview -pickplace insert
  } else {
    chaos:alert -text "You aren't saving any undo information."
  }
}

# chaos-ed_cmds.tcl - most user-visible commands for chaos-ed
#   (preference commands are in chaos-ed_prefs.tcl)
# 
# Copyright 1992-1994 by Jay Sekora.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 
# for non-profit, noncommercial use.

######################################################################
#
# NOTE: these mostly take the arguments "t args", where t is the text
# widget they apply to.  That way they can be used in a chaos:tkb:mkmap
# table (where %W %K %A will be appended to the command before 
# execution) as well as with just %W in bindings.  In a few cases
# where t would be ignored, they just take "args".
#
######################################################################

######################################################################
# view the help file
######################################################################

proc chaos-ed:cmd:help { t args } {
  exec jdoc chaos-ed &
}

######################################################################
# make the about box
######################################################################

proc chaos-ed:cmd:about { t args } {
  global VERSION
  set about_editor [format {
    chaos:rt:hl "chaos-ed"
    chaos:rt:cr
    chaos:rt:rm "by Jay Sekora, "
    chaos:rt:tt "js@bu.edu"
    chaos:rt:par
    chaos:rt:rm "A customisable text editor for X Windows."
    chaos:rt:cr
    chaos:rt:rm "Version %s."
    chaos:rt:par
    chaos:rt:rm "Copyright \251 1992-1994 by Jay Sekora.  "
    chaos:rt:rm "All rights reserved, except that this file may be freely "
    chaos:rt:rm "redistributed in whole or in part for non\255profit, "
    chaos:rt:rm "noncommercial use."
    chaos:rt:par
    chaos:rt:rm "If you find bugs or have suggestions for improvement, "
    chaos:rt:rm "please let me know.  "
    chaos:rt:rm "Feel free to use bits of this code in your own "
    chaos:rt:tt "wish"
    chaos:rt:rm " scripts."
  } $VERSION]
  chaos:about .about $about_editor
  chaos:about:button .about {About chaos-ed} $about_editor
  chaos:about:button .about {About the Author} [chaos:about_jay]
  chaos:about:button .about {About Tk and Tcl} [chaos:about_tktcl]
  
  tkwait window .about
}

######################################################################
# open a new editor window
######################################################################

proc chaos-ed:cmd:new_window { args } {
  chaos-ed:chaos-ed
}

######################################################################
# prompt user for mode
######################################################################

proc chaos-ed:cmd:ask_mode { t args } {
  global MODE
  
  set window [chaos-ed:text_to_top $t]
  set prompt_result [chaos:prompt -text "Editing Mode:"]
  if {$prompt_result != {}} then {
    chaos-ed:set_mode $t $prompt_result
    chaos-ed:apply_mode $window
  }
}

######################################################################
# close a window
######################################################################

proc chaos-ed:cmd:close { t args } {
  global CHAOS-ED_WINDOW_COUNT
  
  if {$CHAOS-ED_WINDOW_COUNT == 1} {
    chaos-ed:cmd:quit $t
  } else {
    set mode [chaos-ed:get_mode $t]
    if {[info procs mode:$mode:pre_close_hook] != {}} {
      mode:$mode:pre_close_hook $t
    }
    
    if {[info procs mode:$mode:close] == {}} {
      if [chaos:confirm -text "Are you sure you want to close this window?"] {
        incr CHAOS-ED_WINDOW_COUNT -1	;# one fewer window
        destroy [chaos-ed:text_to_top $t]
      }
    } else {
      mode:$mode:close $t
    }
  }
}

######################################################################
# quit the editor
######################################################################

proc chaos-ed:cmd:quit { t args } {
  set mode [chaos-ed:get_mode $t]
  
  if {[info procs mode:$mode:pre_quit_hook] != {}} {
    mode:$mode:pre_quit_hook $t
  }
  
  if {[info procs mode:$mode:quit] == {}} {
    if [chaos:confirm -text "Are you sure you want to quit?"] {
      exit 0
    }
  } else {
    mode:$mode:quit $t
  }
}

######################################################################
# read in a file
######################################################################

proc chaos-ed:cmd:load { t args } {
  chaos-ed:cmd:save_checkpoint $t	;# save undo information

  set filename [chaos:fs -prompt "Load:"]
  if {"x$filename" != "x"} then {
    chaos-ed:set_filename $t $filename
    
    # if new filename should have a different mode, set it:
    set old_mode [chaos-ed:get_mode $t]
    set new_mode [chaos-ed:guess_mode $filename]
    if {[string compare $old_mode $new_mode] != 0} {
      chaos-ed:set_mode $t $new_mode
      chaos-ed:apply_mode $t
    }
    
    chaos-ed:read $filename $t
  }
}
  
######################################################################
# write out a file, using window's filename if defined
######################################################################

proc chaos-ed:cmd:save { t args } {
  set filename [chaos-ed:get_filename $t]
  if {"x$filename" != "x"} then {
    chaos-ed:write $filename $t
  } else {
    set filename [chaos:fs -prompt "Save as:"]
    if {"x$filename" != "x"} then {
      chaos-ed:set_filename $t $filename
      chaos-ed:set_label [chaos-ed:text_to_top $t]
      chaos-ed:write $filename $t
    }
  }
}

######################################################################
# write out a file, prompting for a filename
######################################################################

proc chaos-ed:cmd:saveas { t args } {
  set filename [chaos:fs -prompt "Save as:"]
  if {"x$filename" != "x" && \
     ( ! [file exists $filename] || \
      [chaos:confirm -text \
      "File \"$filename\" exists; replace it?"] )} then {
    chaos-ed:set_filename $t $filename
    chaos-ed:set_label [chaos-ed:text_to_top $t]
    chaos-ed:write $filename $t
  }
}

######################################################################
# print the file using lpr
######################################################################

proc chaos-ed:cmd:print { t args } {
  global J_PREFS
  if [chaos:confirm -priority 24 \
    -text "Print using `lpr' to printer `$J_PREFS(printer)'?"] {
    exec lpr -P$J_PREFS(printer) << [$t get 1.0 end]
  }
}

######################################################################
# print rich-text as postscript using lpr
######################################################################

proc chaos-ed:cmd:print_postscript { t args } {
  global J_PREFS
  if [chaos:confirm -priority 24 \
    -text "Print as PostScript using `lpr' to printer `$J_PREFS(printer)'?"] {
    exec lpr -P$J_PREFS(printer) << [chaos:tc:ps:convert_text $t]
  }
}

######################################################################
# read in a file and insert it at the insert mark
######################################################################

proc chaos-ed:cmd:insfile { t args } {
  chaos-ed:cmd:save_checkpoint $t			;# save undo information
  set prompt_result [chaos:fs -prompt "Insert:"]
  if {$prompt_result != {}} then {
    chaos:text:insert_string $t [exec cat $prompt_result]
    chaos:text:insert_string $t "\n"
  }
}

######################################################################
# delete the selection and copy it to CUTBUFFER
######################################################################

proc chaos-ed:cmd:cut { t args } {
  global CUTBUFFER

  chaos-ed:cmd:save_checkpoint $t			;# save undo information

  set CUTBUFFER [$t get sel.first sel.last]
  chaos:text:delete $t sel.first sel.last
}

######################################################################
# copy the selection into CUTBUFFER
######################################################################

proc chaos-ed:cmd:copy { t args } {
  global CUTBUFFER

  set CUTBUFFER [$t get sel.first sel.last]
}

######################################################################
# insert CUTBUFFER
######################################################################

proc chaos-ed:cmd:paste { t args } {
  global CUTBUFFER
  
  set mode [chaos-ed:get_mode $t]
  
  chaos-ed:cmd:save_checkpoint $t			;# save undo information

  if {[info procs mode:$mode:pre_paste_hook] != {}} {
    mode:$mode:pre_paste_hook $t
  }

  chaos:text:insert_string $t $CUTBUFFER

  if {[info procs mode:$mode:post_paste_hook] != {}} {
    mode:$mode:post_paste_hook $t
  }
}

######################################################################
# copy the selection into a text panel (as a note)
######################################################################

proc chaos-ed:cmd:note { t args } {
  chaos:more -title Note -text [$t get sel.first sel.last]
}

######################################################################
# mark the entire text as selected
######################################################################

proc chaos-ed:cmd:select_all { t args } {
  $t tag add sel 1.0 end
}

######################################################################
# prompt for a Unix command to run on the selection
######################################################################

proc chaos-ed:cmd:run_pipe { t args } {
  global UNIX_PIPE; append UNIX_PIPE {}

  set prompt_result [chaos:prompt -text "Unix Filter:" -default $UNIX_PIPE]
  if {$prompt_result != {}} then {
    set UNIX_PIPE $prompt_result
    chaos-ed:pipe $t $UNIX_PIPE		;# handles checkpointing
  }
}

######################################################################
# prompt for a Unix command to insert
######################################################################

proc chaos-ed:cmd:run_command { t args } {
  global UNIX_COMMAND; append UNIX_COMMAND {}

  set prompt_result [chaos:prompt -text "Unix Command:" -default $UNIX_COMMAND]
  if {$prompt_result != {}} then {
    set UNIX_COMMAND $prompt_result
    catch { eval exec $UNIX_COMMAND } result
    if {$result != {}} {
      append result "\n"
      chaos-ed:cmd:save_checkpoint $t			;# save undo information
      chaos:text:insert_string $t $result
    }
  }
}

######################################################################
# expand dynamic abbreviation before insert
######################################################################

proc chaos-ed:cmd:dabbrev { t args } {
  # THIS COULD BE SIMPLIFIED: do i need both match... and abbrev... vars?
  # PROBLEM: this depends on the Text widget's notion of words.
  # it would be nice to be able to expand, say, $tk_l to $tk_library.

  global ABBREV ABBREV_POS MATCH MATCH_POS

  $t mark set abbrevend insert
  $t mark set abbrevstart insert
  while {[$t compare abbrevstart != 1.0] &&
         [string match {[a-zA-Z0-9']} [$t get {abbrevstart - 1 char}]]} {
    $t mark set abbrevstart {abbrevstart -1char}
  }

  set ABBREV_POS [$t index abbrevstart]	;# for dabbrev_again

  set ABBREV [$t get abbrevstart insert]

  set context [$t get 0.0 abbrevstart]

  while {1} {
    set matchpos [string last $ABBREV $context]
  
    if {$matchpos == -1} {return 0}	;# not found

    $t mark set matchstart [$t index "0.0 +$matchpos chars"]
    if {[$t compare matchstart == {matchstart wordstart}]} {
      $t mark set matchend [$t index {matchstart wordend}]
      break				;# sort of an `until'
    }
    set context [$t get 0.0 matchstart]
  }

  set MATCH [$t get matchstart matchend]

  set MATCH_POS [$t index matchstart]

  chaos:text:replace $t abbrevstart abbrevend $MATCH
  return 1
}

# ######################################################################
# # dabbrev_again - search earlier in the text for abbrevs
# #   CURRENTLY NOT USED
# ######################################################################
# 
# proc dabbrev_again { t args } {
#   # THIS COULD BE SIMPLIFIED: do i need both match... and abbrev... vars?
#   # PROBLEM: this depends on the Text widget's notion of words.
#   # it would be nice to be able to expand, say, $tk_l to $tk_library.
# 
#   global ABBREV ABBREV_POS MATCH MATCH_POS
# 
#   set context [$t get 0.0 $MATCH_POS]
# 
#   while {1} {
#     set matchpos [string last $ABBREV $context]
#   
#     if {$matchpos == -1} {
#       return [sabbrev]			;# try the static table
#     }
#     $t mark set matchstart [$t index "0.0 +$matchpos chars"]
#     if {[$t compare matchstart == {matchstart wordstart}]} {
#       $t mark set matchend [$t index {matchstart wordend}]
#       break				;# sort of an `until'
#     }
#     set context [$t get 0.0 matchstart]
#   }
# 
#   set MATCH [$t get matchstart matchend]
# 
#   set MATCH_POS [$t index matchstart]
# 
#   chaos:text:replace $t $ABBREV_POS abbrevend "$MATCH "
# }

######################################################################
# look up and expand static abbrev before insert
######################################################################

proc chaos-ed:cmd:sabbrev { t args } {
  $t mark set abbrevend insert
  # following don't really need to be global (shared with dabbrev):
  global ABBREV ABBREV_POS ABBREVS

  $t mark set abbrevend insert
  $t mark set abbrevstart insert
  while {[$t compare abbrevstart != 1.0] &&
         [string match {[a-zA-Z0-9_']} [$t get {abbrevstart - 1 char}]]} {
    $t mark set abbrevstart {abbrevstart -1char}
  }

  # avoid expanding things like \def, .PP, file.c, etc.:
  set prefix [$t get {abbrevstart -2chars} {abbrevstart}]
  if {[string length $prefix] > 0} {
    if {[string match {?[@$%&+=\:~.]} $prefix]} {
      return 0
    }
    # don't expand "l" in "ls -l", but do expand "this---l"
    if {[string match "\[ \t\n\]-" $prefix]} {	;# don't expand "ls -l"
      return 0
    }
    # don't expand "s" in "house(s)", but do expand "so (s) of"
    if {[string match "\[a-zA-Z](" $prefix]} {	;# don't expand "house(s)"
      return 0
    }
  }

  set ABBREV_POS [$t index abbrevstart]	;# for dabbrev_again

  # first try regular version:
  set ABBREV [$t get abbrevstart insert]
  if {[info exists ABBREVS($ABBREV)]} {
    chaos:text:replace $t $ABBREV_POS abbrevend $ABBREVS($ABBREV)
    return 1
  }
  # else try capitalised version
  if {[string match {[A-Z][a-z]*} $ABBREV]} {
    set lcabbrev [chaos-ed:uncapitalise $ABBREV]
    if {[info exists ABBREVS($lcabbrev)]} {
      chaos:text:replace $t $ABBREV_POS abbrevend \
        [chaos-ed:capitalise $ABBREVS($lcabbrev)]
      return 1
    }
  }
  return 0
}

######################################################################
# edit your abbrevs file
######################################################################

proc chaos-ed:cmd:edit_abbrevs { args } {
  global HOME
  if {! [file isdirectory "$HOME/.tk"]} then {
    exec mkdir "$HOME/.tk"
    # above should have error-checking
  }
  exec jabbrevs "$HOME/.tk/abbrevs.tcl" &	;# doesn't currently use arg
}

######################################################################
# read abbrevs file
######################################################################

proc chaos-ed:cmd:read_abbrevs { args } {
  chaos:source_config abbrevs.tcl
}

######################################################################
# toggle static abbrevs
######################################################################

proc chaos-ed:cmd:toggle_sabbrev { t args } {
  global CHAOS-ED_MODEPREFS
  
  set mode [chaos-ed:get_mode $t]
  
  set CHAOS-ED_MODEPREFS($mode,sabbrev) \
    [expr {! $CHAOS-ED_MODEPREFS($mode,sabbrev)}]
}

######################################################################
# toggle dynamic abbrevs
######################################################################

proc chaos-ed:cmd:toggle_dabbrev { t args } {
  global CHAOS-ED_MODEPREFS
  
  set mode [chaos-ed:get_mode $t]
  
  set CHAOS-ED_MODEPREFS($mode,dabbrev) \
    [expr {! $CHAOS-ED_MODEPREFS($mode,dabbrev)}]
}

######################################################################
# go to a particular line
######## NEED TO CHECK THAT AN INDEX WAS TYPED!
######################################################################

proc chaos-ed:cmd:go_to_line { t args } {
  set prompt_result [chaos:prompt -text "Go to line number:"]
  if {$prompt_result != {}} then {
    chaos-ed:go_to_line $t $prompt_result
  }
}

######################################################################
# display which line the cursor is on
######################################################################

proc chaos-ed:cmd:current_line { t args } {
  set insertindex [split [$t index insert] {.}]
  set line [lindex $insertindex 0]
  set column [lindex $insertindex 1]
  chaos:alert -title "Notice" \
    -text "The insertion point is at line $line, column $column."
}

######################################################################
# insert X selection
######################################################################

proc chaos-ed:cmd:xpaste { t args } {
  set mode [chaos-ed:get_mode $t]
  
  chaos-ed:cmd:save_checkpoint $t			;# save undo information
  
  if {[info procs mode:$mode:pre_xpaste_hook] != {}} {
    mode:$mode:pre_xpaste_hook $t
  }

  chaos:text:insert_string $t [chaos:selection_if_any]

  if {[info procs mode:$mode:post_xpaste_hook] != {}} {
    mode:$mode:post_xpaste_hook $t
  }
}

######################################################################
# front end for chaos:find to match chaos-ed:cmd argument convention
######################################################################

proc chaos-ed:cmd:find { t args } {
  chaos-ed:cmd:save_checkpoint $t
  chaos:find $t
}

######################################################################
# find same string again (same kind of search)
######################################################################

proc chaos-ed:cmd:find_again { t args } {
  chaos-ed:cmd:save_checkpoint $t
  chaos:find:again $t
}

######################################################################
# hacks for more-specific kinds of finds (for vi/emacs bindings)
### BOGUS!  chaos-ed should not need to know about the internals of chaos:find!
######################################################################

proc chaos-ed:cmd:find_forward { t args } {
  global j_find
  set j_find(backwards) 0
  chaos:find $t
}

proc chaos-ed:cmd:find_backward { t args } {
  global j_find
  set j_find(backwards) 1
  chaos:find $t
}

######################################################################
# save all windows and quit
######################################################################

# we need to make sure there's a filename before calling save, because
# a cancel in the saveas file selector box will cancel the save, but
# not the quit!

proc chaos-ed:cmd:done { t args } {
  set mode [chaos-ed:get_mode $t]
  
  if {[info procs mode:$mode:done] == {}} {
    set filename [chaos-ed:get_filename $t]
    if {"x$filename" == "x"} then {
      set filename [chaos:fs -prompt "Save as:"]
      if {"x$filename" == "x"} {			;# user clicked cancel
        return
      } else {
        chaos-ed:set_filename $t $filename
      }
    }

    chaos-ed:cmd:save $t
    chaos-ed:cmd:close $t
  } else {
    mode:$mode:done $t
  }
}

######################################################################
# panel to let user insert any iso-8859 character
######################################################################

proc chaos-ed:cmd:char_panel { t args } {
  set tl [chaos:new_toplevel .high_bit]
  wm title $tl "Characters"
  
  message $tl.m -aspect 350 \
    -text "Click on a character to insert it."
  text $tl.t -width 16 -height 12 -wrap none \
    -cursor top_left_arrow \
    -font -*-courier-bold-r-normal-*-*-140-* \
    -borderwidth 2 -relief groove
  
  # using chaos:buttonbar for visual consistency:  
  chaos:buttonbar $tl.b -buttons {
    {ok Done {}}
  }
  $tl.b.ok configure -command "destroy $tl"
  
  for {set i 32} {$i < 112} {incr i 16} {
    for {set j 0} {$j < 16} {incr j} {
      $tl.t insert end [format %c [expr {$i + $j}]]
    }
    $tl.t insert end "\n"
  }
  for {set j 112} {$j < 127} {incr j} {
    $tl.t insert end [format %c $j]
  }
  $tl.t insert end " \n "
  for {set i 160} {$i < 256} {incr i 16} {
    for {set j 0} {$j < 16} {incr j} {
      $tl.t insert end [format %c [expr {$i + $j}]]
    }
    $tl.t insert end "\n"
  }
  $tl.t configure -state disabled
  
  pack $tl.m -fill x
  pack $tl.t -padx 10
  pack $tl.b -anchor e
  
  bind $tl.t <ButtonRelease-1> "
    chaos:text:insert_string $t \[%W get @%x,%y\]
  "
  foreach event {
    <ButtonRelease-3> <B3-Motion> <Button-3> <ButtonRelease-2>
    <ButtonRelease-1><B2-Motion> <Button-2> <Shift-B1-Motion>
    <Shift-Button-1> <B1-Motion> <Triple-Button-1> <Double-Button-1>
    <Button-1>
    } {
    bind $tl.t $event {;}
  }
}

######################################################################
# insert a hyphen
######################################################################

proc chaos-ed:cmd:hyphen { t args } {
  chaos:text:insert_string $t "\xad"
}

######################################################################
# insert a copyright symbol
######################################################################

proc chaos-ed:cmd:copyright { t args } {
  chaos:text:insert_string $t "\xa9"
}

######################################################################
# rich-text cut
######################################################################

proc chaos-ed:cmd:rich_cut { t } {
  chaos-ed:cmd:rich_copy $t			;# (saves checkpoint)
  $t delete sel.first sel.last
}

######################################################################
# rich-text copy
######################################################################

proc chaos-ed:cmd:rich_copy { t } {
  global RICHBUFFER
  
  chaos-ed:cmd:save_checkpoint $t			;# save undo information
  
  set RICHBUFFER {}
  set curstring {}
  set curtags [$t tag names sel.first]
  
  $t mark set richptr sel.first
  
  while {[$t compare richptr < sel.last]} {
    set tags [$t tag names richptr]
    set char [$t get richptr]
    if {"x$tags" != "x$curtags"} {	;# new "range" of text
      lappend RICHBUFFER [list $curstring $curtags]
      set curstring $char
      set curtags $tags
    } else {
      append curstring $char
    }
    $t mark set richptr {richptr+1c}
  }
  lappend RICHBUFFER [list $curstring $curtags]
  return
}

######################################################################
# rich-text paste
#   partly lifted from insertWithTags in mkStyles.tcl demo
######################################################################

proc chaos-ed:cmd:rich_paste { t } {
  global RICHBUFFER
  
  chaos-ed:cmd:save_checkpoint $t			;# save undo information
  
  lappend RICHBUFFER {}			;# make sure it's defined
  
  foreach pair $RICHBUFFER {
    set text [lindex $pair 0]
    set tags [lindex $pair 1]
    
    set start [$t index insert]
    $t insert insert $text
    foreach tag [$t tag names $start] {
      $t tag remove $tag $start insert	;# clear tags inherited from left
    }
    foreach tag $tags {	
      $t tag add $tag $start insert	;# add new tags
    }
  }
  $t tag remove sel 1.0 end		;# clear selection (guaranteed in text)
  return
}


# chaos-ed_io.tcl - file access procedures for chaos-ed, a tk-based editor
# 
# Copyright 1992-1994 by Jay Sekora.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 
# for non-profit, noncommercial use.

# TO DO
#   abbrev fixes:
#     maybe some heuristics for things like plurals
#     maybe a syntax for suffixes (e.g., commit;t -> commitment)
#   file_modes panel
#   documentation for keybindings (automatic documentation?)
#   problem with filename getting set when you cancel Save 
#     for the first time on a new unnamed file
#   improve find panel
#     have find wrap around (if last time didn't match)
#     regex search/replace
#     find all at once (mark) and cycle through with tag nextrange
#   gesture commands
#   autobreaking space a problem if you use two spaces betw sentences
#   word-end punctuation (and heuristics) sd be mode-specific
#
#   PROBLEM WITH CHANGING BINDINGS ON THE FLY!               (urgent)

# CHANGES:
#   lots of binding changes (jbind*.tcl consistency)
#     app-specific Emacs and vi bindings
#   house(s) the s won't expand
#   return key checkpoints!
#   improved mode handling (hooks)

######################################################################

######################################################################
# "Load..." with supplied filename
######################################################################

proc chaos-ed:read { filename t } {
  global CHAOS-ED_MODEPREFS
  set mode [chaos-ed:get_mode $t]
  if {! [info exists CHAOS-ED_MODEPREFS($mode,savestate)]} {
    set CHAOS-ED_MODEPREFS($mode,savestate) 0
  }
  set mode [chaos-ed:get_mode $t]

  if {[info procs mode:$mode:pre_read_hook] != {}} {
    mode:$mode:pre_read_hook $filename $t
  }
  if {[info procs mode:$mode:read] != {}} {
    mode:$mode:read $filename $t
  } else {
    if {! [file exists $filename]} then {
      chaos-ed:cmd:save_checkpoint $t		;# in case you were editing sth
      chaos:text:delete $t 1.0 end
      chaos:text:move $t 1.0
      chaos-ed:set_label [chaos-ed:text_to_top $t] "$filename (new file)"
    } else {
      chaos-ed:cmd:save_checkpoint $t		;# so you can undo a load
      # should do error checking
      chaos:text:delete $t 1.0 end
      $t insert end  [chaos:fileio:read $filename]
      chaos:text:move $t 1.0
      #
      if $CHAOS-ED_MODEPREFS($mode,savestate) {
        chaos-ed:read_annotation $filename $t
        chaos-ed:yview_insert $t
      }
      chaos-ed:cmd:save_checkpoint $t		;# alows undo to original state
    }
  }
  chaos-ed:set_label [chaos-ed:text_to_top $t]	;# display name over text field
  if {[info procs mode:$mode:post_read_hook] != {}} {
    mode:$mode:post_read_hook $filename $t
  }
}

######################################################################
# write out a file
######################################################################

proc chaos-ed:write { filename t } {
  global CHAOS-ED_MODEPREFS
  set mode [chaos-ed:get_mode $t]
  if {! [info exists CHAOS-ED_MODEPREFS($mode,savestate)]} {
    set CHAOS-ED_MODEPREFS($mode,savestate) 0
  }
  set mode [chaos-ed:get_mode $t]
  
  if {[info procs mode:$mode:pre_write_hook] != {}} {
    mode:$mode:pre_write_hook $filename $t
  }
  if {[info procs mode:$mode:write] != {}} {
    mode:$mode:write $filename $t
  } else {
    # should do error checking
    chaos:fileio:write $filename [$t get 1.0 end]
    chaos-ed:set_label [chaos-ed:text_to_top $t]
    #
    if $CHAOS-ED_MODEPREFS($mode,savestate) {
      chaos-ed:write_annotation $filename $t
    }   
  }
  if {[info procs mode:$mode:post_write_hook] != {}} {
    mode:$mode:post_write_hook $filename $t
  }
}

######################################################################
# write out non-text content of a file
######################################################################

proc chaos-ed:write_annotation { filename t } {
  set dirname [file dirname $filename]
  set tail [file tail $filename]
  set filename "$dirname/.state.$tail"
  # should do error checking
  chaos:fileio:write $filename [chaos:tag:get_annotation $t]
}

######################################################################
# restore non-text content of a file
######################################################################

proc chaos-ed:read_annotation { filename t } {
### NEEDS ERROR CHECKING!
  set dirname [file dirname $filename]
  set tail [file tail $filename]
  set filename "$dirname/.state.$tail"
  catch {
    set state [chaos:fileio:read $filename]
    chaos:tag:set_annotation $t $state
  }
}



# chaos-ed_menus.tcl - menus for chaos-ed, a tk-based editor
# 
# Copyright 1992-1995 by Jay Sekora.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 
# for non-profit, noncommercial use.

######################################################################
# chaos-ed:mkmenus - create menubar
######################################################################

proc chaos-ed:mkmenus {mb t} {
  global CHAOS-ED_MODEPREFS
  
  set mode [chaos-ed:get_mode $t]
  
  set all_menus {editor file edit prefs abbrev filter format mode1 mode2}
  set displayed_menus {}
  
  foreach menu $all_menus {
    if [winfo exists $mb.$menu] {
      destroy $mb.$menu
    }
    if $CHAOS-ED_MODEPREFS($mode,menu,$menu) {
      catch {
        chaos-ed:mkmenu:$menu $mb.$menu $t
        pack $mb.$menu -in $mb -side left
        lappend displayed_menus $mb.$menu
      }
    }
  }
  
  # check for user menu proc - normally in ~/.tk/chaos-edrc.tcl
  #
  if $CHAOS-ED_MODEPREFS($mode,menu,user) {
    if {[info procs chaos-ed:mkmenu:user] != {}} {
      if [winfo exists $mb.user] {
        destroy $mb.user
      }
      chaos-ed:mkmenu:user $mb.user $t
      pack $mb.user -in $mb -side right
      lappend displayed_menus $mb.user
    }
  }
  
  eval tk_menuBar $mb $displayed_menus
}

proc chaos-ed:mkmenu:editor {menu t} {
  global CHAOS-ED_MODEPREFS
  
  menubutton $menu -text {Editor} -menu $menu.m
  
  menu $menu.m
  
  $menu.m add command -label {Help} -accelerator {[h]} \
    -command "chaos-ed:cmd:help $t"
  $menu.m add command -label {About the Editor . . .} \
    -command "chaos-ed:cmd:about $t"
  $menu.m add command -label {Global Preferences . . .} \
    -accelerator {[G]} \
    -command {chaos:global_pref_panel}
  $menu.m add command -label {Editor Preferences . . .} \
    -accelerator {[P]} \
    -command "chaos-ed:cmd:edit_prefs $t"
  $menu.m add command -label {Mode Preferences . . .} \
    -command "chaos-ed:cmd:mode_prefs $t"
  $menu.m add command -label {Mode . . .} -accelerator {[m]} \
    -command "chaos-ed:cmd:ask_mode $t"
  $menu.m add separator
  $menu.m add command -label {Issue Tcl Command . . .} \
    -accelerator {[T]} -command {chaos:prompt_tcl}
  $menu.m add command -label {Issue Unix Command . . .} \
    -accelerator {[U]} -command {chaos:prompt_unix}
  $menu.m add separator
  $menu.m add command -label {New Window} -accelerator {[n]} \
    -command "chaos-ed:cmd:new_window $t"
  $menu.m add command -label {Done} \
    -command "chaos-ed:cmd:done $t"
  $menu.m add command -label {Close Window} -accelerator {[w]} \
    -command "chaos-ed:cmd:close $t"
  $menu.m add command -label {Quit} -accelerator {[q]} \
    -command "chaos-ed:cmd:quit $t"
}

proc chaos-ed:mkmenu:file {menu t} {
  global CHAOS-ED_MODEPREFS
  
  menubutton $menu -text {File} -menu $menu.m
  
  menu $menu.m
  
  $menu.m add command -label {Load . . .} -accelerator {[l]} \
    -command "chaos-ed:cmd:load $t"
  $menu.m add command -label {Save} -accelerator {[s]} \
    -command "chaos-ed:cmd:save $t"
  $menu.m add command -label {Save As . . .} -accelerator {[S]} \
    -command "chaos-ed:cmd:saveas $t"
  $menu.m add command -label {Print . . .} -accelerator {[p]} \
    -command "chaos-ed:cmd:print $t"
  $menu.m add separator
  $menu.m add command -label {Insert File . . .} -accelerator {[i]} \
    -command "chaos-ed:cmd:insfile $t"
}

proc chaos-ed:mkmenu:edit {menu t} {
  global CHAOS-ED_MODEPREFS
  
  menubutton $menu -text {Edit} -menu $menu.m
  
  menu $menu.m
  
  $menu.m add command -label {Cut} -accelerator {[x]} \
    -command "chaos-ed:cmd:cut $t"
  $menu.m add command -label {Copy} -accelerator {[c]} \
    -command "chaos-ed:cmd:copy $t"
  $menu.m add command -label {Paste} -accelerator {[v]} \
    -command "chaos-ed:cmd:paste $t"
  $menu.m add command -label {Note} -accelerator {[N]} \
    -command "chaos-ed:cmd:note $t"
  $menu.m add command -label {Insert X Selection} -accelerator {[V]} \
    -command "chaos-ed:cmd:xpaste $t"
  $menu.m add command -label {Select All} -accelerator {[a]} \
    -command "chaos-ed:cmd:select_all $t"
  $menu.m add separator
  $menu.m add command -label {Find . . .} -accelerator {[f]} \
    -command "chaos-ed:cmd:find $t"
  $menu.m add command -label {Find Again} -accelerator {[g]} \
    -command "chaos-ed:cmd:find_again $t"
  $menu.m add separator
  $menu.m add command -label {Go to Line . . .} -accelerator {[L]} \
    -command "chaos-ed:cmd:go_to_line $t"
  $menu.m add command \
    -label {Show Current Position . . .} -accelerator {[C]} \
    -command "chaos-ed:cmd:current_line $t"
  $menu.m add separator
  #
  # the following three SHOULD BE affected by later configuration, and a trace
  # on CHAOS-ED_PREFS(undolevel) (but aren't)
  #
  $menu.m add command -label {Checkpoint} \
    -command "chaos-ed:cmd:save_checkpoint $t"
  $menu.m add command -label {Undo} -accelerator {[z]} \
    -command "chaos-ed:cmd:undo $t"
  $menu.m add command -label {Redo} -accelerator {[Z]} \
    -command "chaos-ed:cmd:redo $t"
}

proc chaos-ed:mkmenu:prefs {menu t} {
  global CHAOS-ED_MODEPREFS
  
  set mode [chaos-ed:get_mode $t]
  
  menubutton $menu -text {Prefs} -menu $menu.m
  
  menu $menu.m
  
  $menu.m add checkbutton -label {Save/load visual state} \
    -variable CHAOS-ED_MODEPREFS($mode,savestate) \
    -command "chaos-ed:apply_prefs \[chaos-ed:text_to_top $t\]"
  $menu.m add checkbutton -label {Break lines on <space>} \
    -variable CHAOS-ED_MODEPREFS($mode,autobreak) \
    -command "chaos-ed:apply_prefs \[chaos-ed:text_to_top $t\]"
  $menu.m add checkbutton -label {Indent lines on <Return>} \
    -variable CHAOS-ED_MODEPREFS($mode,autoindent) \
    -command "chaos-ed:apply_prefs \[chaos-ed:text_to_top $t\]"
  $menu.m add separator
  $menu.m add radiobutton -label {Don't wrap lines} \
    -variable CHAOS-ED_MODEPREFS($mode,textwrap) -value none \
    -command "chaos-ed:apply_prefs \[chaos-ed:text_to_top $t\]"
  $menu.m add radiobutton -label {Wrap lines anywhere} \
    -variable CHAOS-ED_MODEPREFS($mode,textwrap) -value char \
    -command "chaos-ed:apply_prefs \[chaos-ed:text_to_top $t\]"
  $menu.m add radiobutton -label {Wrap lines at words} \
    -variable CHAOS-ED_MODEPREFS($mode,textwrap) -value word \
    -command "chaos-ed:apply_prefs \[chaos-ed:text_to_top $t\]"
}

proc chaos-ed:mkmenu:abbrev {menu t} {
  global CHAOS-ED_MODEPREFS
  
  set mode [chaos-ed:get_mode $t]
  
  menubutton $menu -text {Abbrev} -menu $menu.m
  
  menu $menu.m
  
  $menu.m add checkbutton -label {Static Abbreviation} \
    -accelerator {[Space]} \
    -variable CHAOS-ED_MODEPREFS($mode,sabbrev) -onvalue 1 -offvalue 0
  $menu.m add checkbutton -label {Dynamic Abbreviation} \
    -accelerator {[Tab]} \
    -variable CHAOS-ED_MODEPREFS($mode,dabbrev) -onvalue 1 -offvalue 0
  $menu.m add separator
  $menu.m add command -label {Expand Static Abbreviation} \
    -accelerator {[']} \
    -command "chaos-ed:cmd:sabbrev $t"
  $menu.m add command -label {Expand Dynamic Abbreviation} \
    -accelerator {[;]} \
    -command "chaos-ed:cmd:dabbrev $t"
  $menu.m add separator
  $menu.m add command -label {Edit Static Abbreviations} \
    -command "chaos-ed:cmd:edit_abbrevs"
  $menu.m add command -label {Reread Static Abbreviations} \
    -command "chaos-ed:cmd:read_abbrevs"
}

proc chaos-ed:mkmenu:filter {menu t} {
  global CHAOS-ED_MODEPREFS
  
  menubutton $menu -text {Filter} -menu $menu.m
  
  menu $menu.m
  
  $menu.m add command -label {Format Lines with `fmt'} \
    -accelerator {[F]} \
    -command "chaos-ed:pipe $t {fmt}"
  $menu.m add separator
  #
  # following few entries are tricky syntactically.  the commands are in
  # quotes, so double-quote-style substitution is done on the ENTIRE
  # command (braces aren't special in quotes).
  #
  $menu.m add command -label {Indent} \
    -accelerator {[]]} \
    -command "chaos-ed:text_regsub $t {(^|\n)} {\\1  }"
  $menu.m add command -label {Quote Email} \
    -command "chaos-ed:text_regsub $t {(^|\n)} {\\1> }"
  $menu.m add command -label {Unindent/Unquote} \
    -accelerator {[[]} \
    -command "chaos-ed:text_regsub $t {(^|\n)\[> \] } {\\1}"
  #
  $menu.m add separator
  $menu.m add command -label {Capitalise} \
    -command "chaos-ed:pipe $t {tr {\[a-z\]} {\[A-Z\]}}"
  $menu.m add command -label {Lowercase} \
    -command "chaos-ed:pipe $t {tr {\[A-Z\]} {\[a-z\]}}"
  $menu.m add command -label {Toggle Case} \
    -command "chaos-ed:pipe $t {tr {\[A-Z\]\[a-z\]} {\[a-z\]\[A-Z\]}}"
  $menu.m add separator
  $menu.m add command -label {Sort by ASCII Sequence} \
    -command "chaos-ed:pipe $t {sort}"
  $menu.m add command -label {Sort Numerically} \
    -command "chaos-ed:pipe $t {sort -n}"
  $menu.m add command -label {Sort Alphabetically} \
    -command "chaos-ed:pipe $t {sort -if}"
  $menu.m add separator
  $menu.m add command -label {Pipe Through . . .} -accelerator {[|]} \
     -command "chaos-ed:cmd:run_pipe $t"
  $menu.m add command -label {Insert Output of . . .} -accelerator {[!]} \
     -command "chaos-ed:cmd:run_command $t"
}

proc chaos-ed:mkmenu:format {menu t} {
  global CHAOS-ED_MODEPREFS chaos-ed_mkmenu_format
  
  menubutton $menu -text {Format} -menu $menu.m
  
  menu $menu.m
  
  chaos-ed:mkmenu:format:font $menu.m.font $t
  chaos-ed:mkmenu:format:background $menu.m.background $t
  chaos-ed:mkmenu:format:foreground $menu.m.foreground $t
  chaos-ed:mkmenu:format:characters $menu.m.characters $t
  
  $menu.m add command -label "Rich Cut" -command "chaos-ed:cmd:rich_cut $t"
  $menu.m add command -label "Rich Copy" -command "chaos-ed:cmd:rich_copy $t"
  $menu.m add command -label "Rich Paste" -command "chaos-ed:cmd:rich_paste $t"
  $menu.m add separator
  $menu.m add cascade -label "Font" -menu $menu.m.font
  $menu.m add cascade -label "Background" -menu $menu.m.background
  $menu.m add cascade -label "Foreground" -menu $menu.m.foreground
  $menu.m add checkbutton -label "Underline" \
    -variable chaos-ed_mkmenu_format(underline) \
    -command "chaos-ed:format:underline $t \$chaos-ed_mkmenu_format(underline)"
  $menu.m add separator
  $menu.m add command -label {Type in Plain} \
    -command "chaos:tag:set_tags $t {}; set chaos-ed_mkmenu_format(underline) 0"
  $menu.m add separator
  $menu.m add cascade -label "Characters" -menu $menu.m.characters
  $menu.m add separator
  $menu.m add command -label "Rich Save As . . ." -command "chaos:tc:saveas $t"
  $menu.m add separator
  $menu.m add command -label "Print PostScript" \
    -command "chaos-ed:cmd:print_postscript $t"
}

proc chaos-ed:mkmenu:format:font {menu t} {
  global CHAOS-ED_MODEPREFS
  
  menu $menu
  
  $menu add command -label {Roman} \
    -accelerator {[R]} \
    -command "chaos-ed:font:roman $t"
  $menu add command -label {Italic} \
    -accelerator {[I]} \
    -command "chaos-ed:font:italic $t"
  $menu add command -label {Bold} \
    -accelerator {[B]} \
    -command "chaos-ed:font:bold $t"
  $menu add command -label {Bold Italic} \
    -accelerator {[X]} \
    -command "chaos-ed:font:bolditalic $t"
  $menu add command -label {Typewriter} \
    -accelerator {[M]} \
    -command "chaos-ed:font:typewriter $t"
  $menu add separator
  $menu add command -label {Level 0 Heading} \
    -command "chaos-ed:font:heading0 $t"
  $menu add command -label {Level 1 Heading} \
    -command "chaos-ed:font:heading1 $t"
  $menu add command -label {Level 2 Heading} \
    -command "chaos-ed:font:heading2 $t"
  $menu add command -label {Level 3 Heading} \
    -command "chaos-ed:font:heading3 $t"
  $menu add command -label {Level 4 Heading} \
    -command "chaos-ed:font:heading4 $t"
  $menu add command -label {Level 5 Heading} \
    -command "chaos-ed:font:heading5 $t"
  $menu add separator
  $menu add command -label {Plain Font} \
    -command "chaos-ed:font:plain $t"
}

proc chaos-ed:mkmenu:format:background {menu t} {
  global CHAOS-ED_MODEPREFS
  
  menu $menu
  
  $menu add command -label {Plain Background} \
    -command "chaos-ed:format:background:clear $t"
  $menu add separator
  
  set colours {
    Black Grey25 Grey33 Grey50 Grey66 Grey75 White
    Red Green Blue Cyan Magenta Yellow
    LemonChiffon Gold SpringGreen
  }
  
  foreach colour $colours {
    $menu add command -label $colour \
      -command [list chaos-ed:format:background $t $colour]
  }
}

proc chaos-ed:mkmenu:format:foreground { menu t } {
  global CHAOS-ED_MODEPREFS
  
  menu $menu
  
  $menu add command -label {Plain Foreground} \
    -command "chaos-ed:format:foreground:clear $t"
  $menu add separator
  
  set colours {
    Black Grey25 Grey33 Grey50 Grey66 Grey75 White
    Red Green Blue Cyan Magenta Yellow
    LemonChiffon Gold SpringGreen
  }
  
  foreach colour $colours {
    $menu add command -label $colour \
      -command [list chaos-ed:format:foreground $t $colour]
  }
}

proc chaos-ed:mkmenu:format:characters { menu t } {
  menu $menu
  
  $menu add command -label "Select Character . . ." \
    -command "chaos-ed:cmd:char_panel $t"
  $menu add command -label "Insert Hyphen" \
    -accelerator {[-]} \
    -command "chaos-ed:cmd:hyphen $t"
  $menu add command -label "Insert Copyright Symbol" \
    -command "chaos-ed:cmd:copyright $t"
}

proc chaos-ed:mkmenu:mode1 { menu t } {
  set mode [chaos-ed:get_mode $t]
  
  #####################  should check for proc, not just catch! ##############
  catch {eval mode:$mode:mkmenu1 $menu $t}
}

proc chaos-ed:mkmenu:mode2 { menu t } {
  set mode [chaos-ed:get_mode $t]
  
  #####################  should check for proc, not just catch! ##############
  catch {eval mode:$mode:mkmenu2 $menu $t}
}

######################################################################
# chaos-ed:menus:prefs w mode- return mode menu preferences metawidget
######################################################################

proc chaos-ed:prefs:menus { w mode } {
  global CHAOS-ED_MODEPREFS
  
  frame $w
  foreach menu {file edit prefs abbrev filter format mode1 mode2 user} {
    checkbutton $w.$menu -relief flat -anchor w \
      -text "Show $menu menu" \
      -variable CHAOS-ED_MODEPREFS($mode,menu,$menu)
    pack $w.$menu -expand y -fill x
  }
  
  return $w
}


# chaos-ed_modes.tcl - mode-handling procedures for chaos-ed, a tk-based editor
# 
# Copyright 1992-1994 by Jay Sekora.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 
# for non-profit, noncommercial use.

# TO DO
#   ELIMINATE REDUNDANCY!  both in the code and in what's done when a mode
#     is entered (I think prefs are being read more than once on startup).
#   abbrev fixes:
#     maybe some heuristics for things like plurals
#     maybe a syntax for suffixes (e.g., commit;t -> commitment)
#   file_modes panel
#   documentation for keybindings (automatic documentation?)
#   problem with filename getting set when you cancel Save 
#     for the first time on a new unnamed file
#   improve find panel
#     have find wrap around (if last time didn't match)
#     regex search/replace
#     find all at once (mark) and cycle through with tag nextrange
#   gesture commands
#   autobreaking space a problem if you use two spaces betw sentences
#   word-end punctuation (and heuristics) sd be mode-specific
#
#   PROBLEM WITH CHANGING BINDINGS ON THE FLY!               (urgent)

# CHANGES:
#   lots of binding changes (jbind*.tcl consistency)
#     app-specific Emacs and vi bindings
#   house(s) the s won't expand
#   return key checkpoints!
#   improved mode handling (hooks)

######################################################################

######################################################################
# chaos-ed:guess_mode f - guess mode based on filename f
######################################################################

proc chaos-ed:guess_mode { f } {
  chaos:debug "chaos-ed:guess_mode $f"
  global FILE_MODES LINE_MODES
  
  #
  # first, try matching on name
  #
  foreach i $FILE_MODES {
    if [string match [lindex $i 0] $f] {
      return [lindex $i 1]
    }
  }
  #
  # then, check first line (might be a script)
  #
  if {[file exists $f]} {
    set file [open $f {r}]
    set line1 [read $file 80]		;# unix sees 32 chars, but be generous
    close $file
    foreach i $LINE_MODES {
      if [string match [lindex $i 0] $line1] {
        return [lindex $i 1]
      }
    }
  }
  #
  # no matches - just use `plain'
  #
  return plain
}

######################################################################
# chaos-ed:read_mode_prefs m - read prefs in $CHAOS-ED_MODEPREFS for mode m
#   Note that the defaults _can't_ be in $jstools_library/chaos-edmodes .
######################################################################

proc chaos-ed:read_mode_prefs { {m plain} } {
  chaos:debug "Reading mode prefs for mode $m."
  global CHAOS-ED_MODEPREFS HOME
  chaos:read_prefs -array CHAOS-ED_MODEPREFS -prefix $m \
    -directory $HOME/.tk/chaos-edmodes -file ${m}-defaults {
    {textfont default}
    {textwidth 80}
    {textheight 24}
    {textwrap char}
    {sabbrev 0}
    {dabbrev 0}
    {autobreak 0}
    {autoindent 0}
    {parenflash 0}
    {savestate 0}
    {buttonbar 1}
    {menu,editor 1}
    {menu,file 1}
    {menu,edit 1}
    {menu,prefs 0}
    {menu,abbrev 1}
    {menu,filter 1}
    {menu,format 0}
    {menu,mode1 0}
    {menu,mode2 0}
    {menu,user 1}
  }
}

######################################################################
# chaos-ed:set_default_mode_prefs mode -
#   set defaults for all mode-specific preferences, so that failure
#   of a mode to specify a particular preference doesn't trigger
#   "no such variable" errors.  doesn't actually read a file.
######################################################################

proc chaos-ed:set_default_mode_prefs { mode } {
  global CHAOS-ED_MODEPREFS
  
  set CHAOS-ED_MODEPREFS($mode,textfont) default
  set CHAOS-ED_MODEPREFS($mode,textwidth) 80
  set CHAOS-ED_MODEPREFS($mode,textheight) 24
  set CHAOS-ED_MODEPREFS($mode,textwrap) char
  set CHAOS-ED_MODEPREFS($mode,sabbrev) 0
  set CHAOS-ED_MODEPREFS($mode,dabbrev) 0
  set CHAOS-ED_MODEPREFS($mode,autobreak) 0
  set CHAOS-ED_MODEPREFS($mode,autoindent) 0
  set CHAOS-ED_MODEPREFS($mode,autoindent) 0
  set CHAOS-ED_MODEPREFS($mode,parenflash) 0
  set CHAOS-ED_MODEPREFS($mode,buttonbar) 1
  set CHAOS-ED_MODEPREFS($mode,menu,editor) 1
  set CHAOS-ED_MODEPREFS($mode,menu,file) 1
  set CHAOS-ED_MODEPREFS($mode,menu,edit) 1
  set CHAOS-ED_MODEPREFS($mode,menu,prefs) 0
  set CHAOS-ED_MODEPREFS($mode,menu,abbrev) 1
  set CHAOS-ED_MODEPREFS($mode,menu,filter) 1
  set CHAOS-ED_MODEPREFS($mode,menu,format) 0
  set CHAOS-ED_MODEPREFS($mode,menu,mode1) 0
  set CHAOS-ED_MODEPREFS($mode,menu,mode2) 0
  set CHAOS-ED_MODEPREFS($mode,menu,user) 1
}

######################################################################
# mode:plain:init - setup for plain mode
#   the presence of this proc guarantees that chaos-ed won't ever need
#   to look for a "plain-mode.tcl" file.  (the same technique could
#   be used by applications that embed chaos-ed and need to modify its
#   behaviour.)
######################################################################

proc mode:plain:init { t } {
  global CHAOS-ED_MODEPREFS
  
  chaos:read_prefs -array CHAOS-ED_MODEPREFS -prefix plain \
    -directory ~/.tk/chaos-edmodes -file plain-defaults {
    {textfont default}
    {textwidth 80}
    {textheight 24}
    {textwrap char}
    {sabbrev 0}
    {dabbrev 0}
    {autobreak 0}
    {autoindent 0}
    {parenflash 0}
    {savestate 0}
    {buttonbar 1}
    {menu,editor 1}
    {menu,file 1}
    {menu,edit 1}
    {menu,prefs 0}
    {menu,abbrev 1}
    {menu,filter 1}
    {menu,format 0}
    {menu,mode1 0}
    {menu,mode2 0}
    {menu,user 1}
  }
}

######################################################################
# chaos-ed:apply_mode -  apply current mode for window (menus, etc.)
# the window can be specified either as a text widget, or as that
# text widget's corresponding toplevel window.
######################################################################

proc chaos-ed:apply_mode { w } {
  chaos:debug "chaos-ed:apply_mode $w"
  global HOME CHAOS-ED_MODEPREFS tk_library jstools_library
  
  if { [winfo class $w] == "Text" } {
    set window [chaos-ed:text_to_top $w]
    set text $w
  } else {
    set window $w
    set text [chaos-ed:top_to_text $w]
  }
  set mode [chaos-ed:get_mode $window]
  set menubar [chaos-ed:top_to_menubar $window]
  set buttonbar [chaos-ed:top_to_buttonbar $window]
  
  if [winfo exists $buttonbar] {
    destroy $buttonbar
  }
  
  foreach key {0 1 2 3 4 5 6 7 8 9} {
    bind $text <Meta-Key-$key> { }
  }
  
  chaos-ed:set_default_mode_prefs $mode
  
  if {"x[info procs mode:${mode}:init]" == "x"} {
    # we don't already have procs to enter the mode, so
    # look through a list of directories searching for the mode file:
    #
    set file ${mode}-mode.tcl
    foreach directory [list \
      $HOME/.tk/chaos-edmodes \
      $jstools_library/chaos-edmodes \
      $jstools_library/chaos-ed/chaos-edmodes \
    ] {
      if [file isfile $directory/$file] {
        chaos:debug "Reading $file in $directory."
        chaos:source_config -directory $directory $file
        break
      }
    }
  }
  mode:${mode}:init $text
  chaos-ed:mkmenus $menubar $text
  if $CHAOS-ED_MODEPREFS($mode,buttonbar) {
    chaos-ed:mkbuttonbar $buttonbar $text
    pack $buttonbar -after $menubar -fill x
  }
  if $CHAOS-ED_MODEPREFS($mode,parenflash) {
    chaos-ed:balance_bind $text
  }
  chaos-ed:configure_text $text
  chaos-ed:set_mode_label $window $mode
}

######################################################################
# set the mode a particular window is in
# the window can be specified either as a text widget, or as that
# text widget's corresponding toplevel window.
######################################################################

proc chaos-ed:set_mode { w newmode } {
  chaos:debug
  global MODES HOME
  
  if { [winfo class $w] == "Text" } {
    set window [chaos-ed:text_to_top $w]
    set text $w
  } else {
    set window $w
    set text [chaos-ed:top_to_text $w]
  }
  
  # do any cleanup necessary to cancel effect of current mode
  set oldmode plain
  catch {set oldmode $MODES($window)}
  if {[info procs mode:$oldmode:cleanup] != {}} {
    catch {mode:$oldmode:cleanup $text}
  }
  
  set MODES($window) $newmode
}

######################################################################
# return the mode a particular window is in
# the window can be specified either as a text widget, or as that
# text widget's corresponding toplevel window.  if no mode has been
# set for that window, returns "plain".
######################################################################

proc chaos-ed:get_mode { w } {
#  chaos:debug
  global MODES
  
  if { [winfo class $w] == "Text" } {
    set window [chaos-ed:text_to_top $w]
#    set text $w
  } else {
    set window $w
#    set text [chaos-ed:top_to_text $w]
  }
  
  if [info exists MODES($window)] {
    return $MODES($window)
  } else {
    return {plain}
  }
}


# chaos-ed_prefs.tcl - preferences commands and procs for chaos-ed
#   (chaos-ed:prefs:menus is in chaos-ed_menus.tcl, for convenience.)
# 
# Copyright 1992-1994 by Jay Sekora.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 
# for non-profit, noncommercial use.

# TO DO
#   MAKE ALL THIS PER-WINDOW!
#   file_modes panel
#   word-end punctuation (and heuristics) sd be mode-specific

######################################################################



######################################################################
# editor-wide preferences panel
#   { t args } lets it be used with chaos:tkb:mkmap
######################################################################

proc chaos-ed:cmd:edit_prefs { t args } {
  global CHAOS-ED_PREFS
  
  set w .edit_prefs
  toplevel $w
  wm title $w "Editor Preferences"
  
  chaos:colour_chooser $w.textbg -variable CHAOS-ED_PREFS(textbg) \
    -label "Normal Background:"
  chaos:colour_chooser $w.textfg -variable CHAOS-ED_PREFS(textfg) \
    -label "Normal Foreground:"
  chaos:colour_chooser $w.textsb -variable CHAOS-ED_PREFS(textsb) \
    -label "Selected Background:"
  chaos:colour_chooser $w.textsf -variable CHAOS-ED_PREFS(textsf) \
    -label "Selected Foreground:"
  
  label $w.textiw-label -text "Insert Width:" -anchor w
  scale $w.textiw -from 1 -to 25 -orient horizontal \
    -command {set CHAOS-ED_PREFS(textiw)}
  $w.textiw set $CHAOS-ED_PREFS(textiw)
  
  label $w.textsbw-label -text "Selection Border Width:" -anchor w
  scale $w.textsbw -from 0 -to 25  -orient horizontal \
    -command {set CHAOS-ED_PREFS(textsbw)}
  $w.textsbw set $CHAOS-ED_PREFS(textsbw)
  
  label $w.textbw-label -text "Text Border Width:" -anchor w
  scale $w.textbw -from 0 -to 50  -orient horizontal \
    -command {set CHAOS-ED_PREFS(textbw)}
  $w.textbw set $CHAOS-ED_PREFS(textbw)
  
  label $w.undolevels-label -text "Undo Levels:" -anchor w
  scale $w.undolevels -from 0 -to 10  -orient horizontal \
    -command {set CHAOS-ED_PREFS(undolevels)}
  $w.undolevels set $CHAOS-ED_PREFS(undolevels)
  
  chaos:buttonbar $w.b -default save -buttons [format {
    {
      save Save {
        chaos:write_prefs -array CHAOS-ED_PREFS -directory $env(HOME)/.tk \
          -file chaos-ed-defaults
        %s.b.done invoke
      }
    } {
      done Done {
        chaos-ed:apply_all_prefs [chaos-ed:text_to_top %s]
        destroy %s
      }
    }
  } $w $t $w]
  
  pack \
    $w.textbg \
    [chaos:rule $w] \
    $w.textfg \
    [chaos:rule $w] \
    $w.textsb \
    [chaos:rule $w] \
    $w.textsf \
    [chaos:rule $w] \
    $w.textiw-label $w.textiw \
    [chaos:filler $w] \
    $w.textsbw-label $w.textsbw \
    [chaos:filler $w] \
    $w.textbw-label $w.textbw \
    [chaos:rule $w] \
    $w.undolevels-label $w.undolevels \
    [chaos:rule $w] \
    $w.b \
    -fill x
  
  chaos:dialogue $w
  chaos:default_button $w.b.save $w
  focus $w
  tkwait window $w
}
######################################################################
# chaos-ed:cmd:mode_prefs - mode-specific preferences panel
#   { t args } lets it be used with chaos:tkb:mkmap
######################################################################

proc chaos-ed:cmd:mode_prefs { t args } {
  global CHAOS-ED_MODEPREFS env tk_strictMotif
  
  set mode [chaos-ed:get_mode $t]
  
  set window [chaos-ed:text_to_top $t]

  toplevel .mode_prefs
  wm title .mode_prefs "Mode\255Specific Preferences"
  
  label .mode_prefs.mode -text "Preferences for mode \"$mode\""
  
  pack .mode_prefs.mode -expand y -fill x
  
  chaos:buttonbar .mode_prefs.b -default save -buttons [format {
    {
      save Save {
        set tmp_mode %s
        chaos:write_prefs -array CHAOS-ED_MODEPREFS -prefix $tmp_mode \
          -directory $env(HOME)/.tk/chaos-edmodes \
          -file ${tmp_mode}-defaults
        .mode_prefs.b.done invoke
      }
    } {
      done Done {
        set tmp_mode %s
        if {$CHAOS-ED_MODEPREFS($tmp_mode,textwidth) < 20} {
          set CHAOS-ED_MODEPREFS($tmp_mode,textwidth) 20
        }
        if {$CHAOS-ED_MODEPREFS($tmp_mode,textheight) < 4} {
          set CHAOS-ED_MODEPREFS($tmp_mode,textheight) 4
        }
        chaos-ed:apply_all_prefs %s
        destroy .mode_prefs
      }
    }
  } $mode $mode $window]
  
  frame .mode_prefs.ui_prefs
  lower .mode_prefs.ui_prefs
  frame .mode_prefs.other_prefs
  lower .mode_prefs.other_prefs
  pack \
    [chaos:rule .mode_prefs] \
    [chaos-ed:prefs:menus .mode_prefs.menus $mode] \
    [chaos:rule .mode_prefs] \
    [chaos-ed:prefs:buttonbar .mode_prefs.buttonbar $mode] \
    -in .mode_prefs.ui_prefs -fill both
  pack \
    [chaos:rule .mode_prefs] \
    [chaos-ed:prefs:io .mode_prefs.io $mode] \
    [chaos:rule .mode_prefs] \
    [chaos-ed:prefs:autokeys .mode_prefs.autokeys $mode] \
    [chaos:rule .mode_prefs] \
    [chaos-ed:prefs:abbrevs .mode_prefs.abbrevs $mode] \
    [chaos:rule .mode_prefs] \
    [chaos-ed:prefs:wrap .mode_prefs.wrap $mode] \
    [chaos:rule .mode_prefs] \
    [chaos-ed:prefs:font .mode_prefs.font $mode] \
    [chaos:rule .mode_prefs] \
    [chaos-ed:prefs:size .mode_prefs.size $mode] \
    -in .mode_prefs.other_prefs -fill both
  pack \
    .mode_prefs.b \
    [chaos:rule .mode_prefs] \
    -fill x -side bottom
  pack \
    .mode_prefs.ui_prefs \
    [chaos:rule .mode_prefs] \
    .mode_prefs.other_prefs \
    -side left -fill y
  
  chaos:dialogue .mode_prefs		;# position in centre of screen

  focus .mode_prefs
  chaos:default_button .mode_prefs.b.save \
    .mode_prefs.font.bot.e \
    .mode_prefs.size.we \
    .mode_prefs.size.he \
    .mode_prefs

  chaos:tab_ring \
    .mode_prefs.font.bot.e \
    .mode_prefs.size.we \
    .mode_prefs.size.he
  
  bind .mode_prefs <Key-Tab> {focus .mode_prefs.font.bot.e}
  tkwait window .mode_prefs
}

proc chaos-ed:prefs:buttonbar { w mode } {
  global CHAOS-ED_MODEPREFS
  
  frame $w
  checkbutton $w.cb -relief flat -anchor w \
    -text {Show button bar} \
    -variable CHAOS-ED_MODEPREFS($mode,buttonbar)
  pack $w.cb -side top -expand yes -fill x
  
  return $w
}

proc chaos-ed:prefs:io { w mode } {
  global CHAOS-ED_MODEPREFS
  
  frame $w
  checkbutton $w.cb -relief flat -anchor w \
    -text {Save/load highlighting and position} \
    -variable CHAOS-ED_MODEPREFS($mode,savestate)
  pack $w.cb -side top -expand yes -fill x
  
  return $w
}

proc chaos-ed:prefs:autokeys { w mode } {
  global CHAOS-ED_MODEPREFS
  
  frame $w
  checkbutton $w.autobreak_cb -relief flat -anchor w \
    -text {Break long lines with <Space>} \
    -variable CHAOS-ED_MODEPREFS($mode,autobreak)
  checkbutton $w.autoindent_cb -relief flat -anchor w \
    -text {Preserve indentation with <Return>} \
    -variable CHAOS-ED_MODEPREFS($mode,autoindent)
  checkbutton $w.parenflash_cb -relief flat -anchor w \
    -text {Flash matching braces, brackets, and parentheses} \
    -variable CHAOS-ED_MODEPREFS($mode,parenflash)
  pack \
    $w.autobreak_cb \
    $w.autoindent_cb \
    $w.parenflash_cb \
    -side top -expand yes -fill x
  
  return $w
}

proc chaos-ed:prefs:abbrevs { w mode } {
  global CHAOS-ED_MODEPREFS
  
  frame $w
  checkbutton $w.sabbrev_cb -relief flat -anchor w \
    -text {Expand static abbreviations with <Space>} \
    -variable CHAOS-ED_MODEPREFS($mode,sabbrev)
  checkbutton $w.dabbrev_cb -relief flat -anchor w \
    -text {Expand dynamic abbreviations with <Tab>} \
    -variable CHAOS-ED_MODEPREFS($mode,dabbrev)
  pack \
    $w.sabbrev_cb \
    $w.dabbrev_cb \
    -side top -expand yes -fill x
  
  return $w
}

proc chaos-ed:prefs:wrap { w mode } {
  global CHAOS-ED_MODEPREFS
  
  frame $w
  radiobutton $w.none -relief flat -anchor w \
    -text {Don't wrap lines} \
    -variable CHAOS-ED_MODEPREFS($mode,textwrap) -value none
  radiobutton $w.char -relief flat -anchor w \
    -text {Wrap lines on character boundaries} \
    -variable CHAOS-ED_MODEPREFS($mode,textwrap) -value char
  radiobutton $w.word -relief flat -anchor w \
    -text {Wrap lines at word boundaries} \
    -variable CHAOS-ED_MODEPREFS($mode,textwrap) -value word
  pack \
    $w.none \
    $w.char \
    $w.word \
    -side top -expand yes -fill x
  
  return $w
}

proc chaos-ed:prefs:font { w mode } {
  global CHAOS-ED_MODEPREFS
  
  frame $w
  
  frame $w.top
  label $w.top.l -text {Font:}
  button $w.top.default -width 8 -text {Default} -command {
    set CHAOS-ED_MODEPREFS($mode,textfont) {default}
  }
  button $w.top.choose -text {Choose . . .} -command {
    set CHAOS-ED_MODEPREFS($mode,textfont) [chaos:prompt_font]
  }
  
  frame $w.bot
  entry $w.bot.e -relief sunken -width 50 \
    -textvariable CHAOS-ED_MODEPREFS($mode,textfont)
  
  pack $w.top.l -side left
  pack $w.top.choose -side right -padx 10 -pady 5
  pack $w.top.default -side right -pady 5
  
  pack $w.bot.e -side left -padx 10 -pady 5
  
  pack \
    $w.top \
    $w.bot \
    -side top -expand yes -fill x
  
  return $w
}

proc chaos-ed:prefs:size { w mode } {
  global CHAOS-ED_MODEPREFS
  
  frame $w
  label $w.wl -text {Width:}
  entry $w.we -relief sunken -width 5 \
    -textvariable CHAOS-ED_MODEPREFS($mode,textwidth)
  label $w.hl -text {Height:}
  entry $w.he -relief sunken -width 5 \
    -textvariable CHAOS-ED_MODEPREFS($mode,textheight)
  
  pack $w.wl -side left -fill x -pady 5
  pack $w.we -side left -pady 5
  pack $w.hl -side left -fill x -pady 5
  pack $w.he -side left -pady 5
  
  return $w
}


# chaos-ed_tags.tcl - text tag-manipulation routines for chaos-ed, a tk-based editor
# 
# Copyright 1992-1994 by Jay Sekora.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 
# for non-profit, noncommercial use.

######################################################################
# font commands - these set the font (tag list) for typing.
#   also, if there is a selection, and the insertion point is in it
#   or abuts it, the selection is set to the specified font.
######################################################################

######################################################################
# chaos-ed:set_tags t tags - general routine to do the above for any tag
######################################################################

proc chaos-ed:set_tags { t args } {
  foreach tag $args {
    chaos:tag:set_tag $t $tag
  }
  if [chaos:text:insert_touches_selection $t] {
    foreach tag $args {
      chaos:tag:tag_text $t $tag sel.first sel.last
    }
  }
}

######################################################################
# chaos-ed:clear_tags t patterns - 
#   remove tags matching any pattern from tag list, and if appropriate,
#   from selection
######################################################################

proc chaos-ed:clear_tags { t args } {
  foreach pattern $args {
    chaos:tag:clear_tag $t $pattern
  }
  if [chaos:text:insert_touches_selection $t] {
    foreach pattern $args {
      chaos:tag:untag_text $t $pattern sel.first sel.last
    }
  }
}

######################################################################
# chaos-ed:font:configure_fonts w - set rich-text fonts
#   should look at preferences
######################################################################

proc chaos-ed:font:configure_fonts { w } {
  chaos:rt:textfonts $w {
    {roman {
        -adobe-helvetica-medium-r-normal-*-*-120-*-*-*-*-*-*
      }
    }
    {italic {
        -adobe-helvetica-medium-o-normal-*-*-120-*-*-*-*-*-*
      }
    }
    {bold {
       -adobe-helvetica-bold-r-normal-*-*-120-*-*-*-*-*-*
      }
    }
    {bolditalic {
        -adobe-helvetica-bold-o-normal-*-*-120-*-*-*-*-*-*
      }
    }
    {typewriter {
        -adobe-courier-medium-r-normal-*-*-120-*-*-*-*-*-*
      }
    }
    {heading0 {
        -b&h-lucida-bold-i-normal-*-*-240-*-*-*-*-*-*
        -adobe-helvetica-bold-o-normal-*-*-240-*-*-*-*-*-*
      }
    }
    {heading1 {
        -b&h-lucida-bold-i-normal-*-*-180-*-*-*-*-*-*
        -adobe-helvetica-bold-o-normal-*-*-180-*-*-*-*-*-*
      }
    }
    {heading2 {
        -b&h-lucida-bold-i-normal-*-*-140-*-*-*-*-*-*
        -adobe-helvetica-bold-o-normal-*-*-140-*-*-*-*-*-*
      }
    }
    {heading3 {
        -b&h-lucida-bold-i-normal-*-*-120-*-*-*-*-*-*
        -adobe-helvetica-bold-o-normal-*-*-120-*-*-*-*-*-*
      }
    }
    {heading4 {
        -b&h-lucida-bold-i-normal-*-*-100-*-*-*-*-*-*
        -adobe-helvetica-bold-o-normal-*-*-100-*-*-*-*-*-*
      }
    }
    {heading5 {
        -b&h-lucida-bold-i-normal-*-*-80-*-*-*-*-*-*
        -adobe-helvetica-bold-o-normal-*-*-80-*-*-*-*-*-*
      }
    }
  }
}

######################################################################
# font procedures
######################################################################

proc chaos-ed:font:roman { t } {
  chaos-ed:set_tags $t richtext:font:roman
}

proc chaos-ed:font:italic { t } {
  chaos-ed:set_tags $t richtext:font:italic
}

proc chaos-ed:font:bold { t } {
  chaos-ed:set_tags $t richtext:font:bold
}

proc chaos-ed:font:bolditalic { t } {
  chaos-ed:set_tags $t richtext:font:bolditalic
}

proc chaos-ed:font:typewriter { t } {
  chaos-ed:set_tags $t richtext:font:typewriter
}

proc chaos-ed:font:heading0 { t } {
  chaos-ed:set_tags $t richtext:font:heading0
}

proc chaos-ed:font:heading1 { t } {
  chaos-ed:set_tags $t richtext:font:heading1
}

proc chaos-ed:font:heading2 { t } {
  chaos-ed:set_tags $t richtext:font:heading2
}

proc chaos-ed:font:heading3 { t } {
  chaos-ed:set_tags $t richtext:font:heading3
}

proc chaos-ed:font:heading4 { t } {
  chaos-ed:set_tags $t richtext:font:heading4
}

proc chaos-ed:font:heading5 { t } {
  chaos-ed:set_tags $t richtext:font:heading5
}

proc chaos-ed:font:plain { t } {
  chaos-ed:clear_tags $t richtext:font:*
}

######################################################################
# other procedures
######################################################################

proc chaos-ed:format:background { t colour } {
  chaos-ed:set_tags $t display:background:$colour
}

proc chaos-ed:format:foreground { t colour } {
  chaos-ed:set_tags $t display:foreground:$colour
}

proc chaos-ed:format:underline { t state } {
  if $state {
    chaos-ed:set_tags $t display:underline:1
  } else {
    chaos-ed:clear_tags $t display:underline:*
  }
}

proc chaos-ed:format:background:clear { t } {
  chaos-ed:clear_tags $t display:background:*
}

proc chaos-ed:format:foreground:clear { t } {
  chaos-ed:clear_tags $t display:foreground:*
}

# chaos-ed_typing.tcl - special typing procedures for chaos-ed, a tk-based editor
# 
# Copyright 1992-1994 by Jay Sekora.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 
# for non-profit, noncommercial use.

# TO DO
#   abbrev fixes:
#     maybe some heuristics for things like plurals
#     maybe a syntax for suffixes (e.g., commit;t -> commitment)
#   file_modes panel
#   documentation for keybindings (automatic documentation?)
#   problem with filename getting set when you cancel Save 
#     for the first time on a new unnamed file
#   improve find panel
#     have find wrap around (if last time didn't match)
#     regex search/replace
#     find all at once (mark) and cycle through with tag nextrange
#   gesture commands
#   autobreaking space a problem if you use two spaces betw sentences
#   word-end punctuation (and heuristics) sd be mode-specific
#
#   PROBLEM WITH CHANGING BINDINGS ON THE FLY!               (urgent)

# CHANGES:
#   lots of binding changes (jbind*.tcl consistency)
#     app-specific Emacs and vi bindings
#   house(s) the s won't expand
#   return key checkpoints!
#   improved mode handling (hooks)

######################################################################

######################################################################
# chaos-ed:self_insert_punct - specialised version of chaos:tkb:self_insert
#   THERE SHOULD BE A GENERALISED MECHANISM FOR THIS!
######################################################################

proc chaos-ed:self_insert_punct { W K A } {
  global j_teb

  if {"$A" != ""} {
    chaos-ed:sabbrev_hook $W
    chaos:tkb:repeatable {
      chaos:text:insert_string $W $A
    } $W
  }
}

######################################################################
# chaos-ed:tabkey - do whatever tab does (abbrev, indent, whatever)
######################################################################

proc chaos-ed:tabkey { t args } {
  global CHAOS-ED_MODEPREFS
  
  set mode [chaos-ed:get_mode $t]
  
  if {[info procs mode:$mode:pre_tabkey_hook] != {}} {
    mode:$mode:pre_tabkey_hook $t
  }
  #
  if {[info procs mode:$mode:tabkey] != {}} {
    mode:$mode:tabkey $t
  } else {
    if $CHAOS-ED_MODEPREFS($mode,dabbrev) {
      chaos-ed:cmd:dabbrev $t
    } else {
      chaos:tkb:self_insert $t Tab "\t"
    }
  }
  #
  if {[info procs mode:$mode:post_tabkey_hook] != {}} {
    mode:$mode:post_tabkey_hook $t
  }
}

######################################################################
# chaos-ed:spacebar - do whatever space does (abbrev, line breaking, whatever)
######################################################################

proc chaos-ed:spacebar { t args } {
  set mode [chaos-ed:get_mode $t]
  
  if {[info procs mode:$mode:pre_spacebar_hook] != {}} {
    mode:$mode:pre_spacebar_hook $t
  }
  #
  if {[info procs mode:$mode:spacebar] != {}} {
    mode:$mode:spacebar $t
  } else {
    chaos-ed:sabbrev_hook $t
    chaos:tkb:self_insert $t space " "
    chaos-ed:autobreak_hook $t
  }
  #
  if {[info procs mode:$mode:post_spacebar_hook] != {}} {
    mode:$mode:post_spacebar_hook $t
  }
}

######################################################################
# chaos-ed:sabbrev_hook t - chaos-ed:cmd:sabbrev if it's on
######################################################################

proc chaos-ed:sabbrev_hook { t } {
  global CHAOS-ED_MODEPREFS
  
  set mode [chaos-ed:get_mode $t]
  
  if $CHAOS-ED_MODEPREFS($mode,sabbrev) {
    chaos-ed:cmd:sabbrev $t
  }
}

######################################################################
# chaos-ed:dabbrev_hook t - chaos-ed:cmd:dabbrev if it's on
######################################################################
# (not used by plain mode - Tab does dabbrev *INSTEAD OF* inserting
#   tab, not *before* inserting tab)

proc chaos-ed:dabbrev_hook { t } {
  global CHAOS-ED_MODEPREFS
  
  set mode [chaos-ed:get_mode $t]

  if $CHAOS-ED_MODEPREFS($mode,dabbrev) {
    chaos-ed:cmd:dabbrev $t
  }
}

######################################################################
# chaos-ed:autobreak_hook - insert a cr if line is long enough
######################################################################

proc chaos-ed:autobreak_hook { t } {
  global CHAOS-ED_MODEPREFS
  
  set mode [chaos-ed:get_mode $t]
  
  if $CHAOS-ED_MODEPREFS($mode,autobreak) {
    set length [string length [$t get {insert linestart} insert]]
    if {$length > ($CHAOS-ED_MODEPREFS($mode,textwidth) - 15)} {
      chaos-ed:returnkey $t
    }
  }
}

######################################################################
# chaos-ed:returnkey - do whatever return does (indentation, etc.)
######################################################################

proc chaos-ed:returnkey { t args } {
  set mode [chaos-ed:get_mode $t]
  
  chaos-ed:cmd:save_checkpoint $t
  
  if {[info procs mode:$mode:pre_returnkey_hook] != {}} {
    mode:$mode:pre_returnkey_hook $t
  }
  #
  if {[info procs mode:$mode:returnkey] != {}} {
    mode:$mode:returnkey $t
  } else {
    chaos-ed:sabbrev_hook $t
    chaos:tkb:self_insert $t Return "\n"
    chaos-ed:autoindent $t
  }
  #
  if {[info procs mode:$mode:post_returnkey_hook] != {}} {
    mode:$mode:post_returnkey_hook $t
  }
}

######################################################################
# chaos-ed:autoindent - insert same indentation as previous line
######################################################################

proc chaos-ed:autoindent { t } {
  global CHAOS-ED_MODEPREFS
  
  set mode [chaos-ed:get_mode $t]
  
  if $CHAOS-ED_MODEPREFS($mode,autoindent) {
    if {[info procs mode:$mode:autoindent] != {}} {
      mode:$mode:autoindent $t
    } else {
      set prevline [$t get {insert -1lines linestart} {insert -1lines lineend}]
      if [regexp "^\[ \t\]\[ \t\]*" $prevline indentation] {
        chaos:text:insert_string $t $indentation
      }
    }
  }
}


# chaos-ed_ui.tcl - user interface for chaos-ed
# 
# Copyright 1992-1994 by Jay Sekora.  All rights reserved, except 
# that this file may be freely redistributed in whole or in part 
# for non-profit, noncommercial use.

######################################################################
# create main window
######################################################################

proc chaos-ed:mkwindow { window } {
  chaos:debug
  global argv0 MODE
  
  set prefix [chaos-ed:top_to_prefix $window]
  
  set menu $prefix.menu
  set main $prefix.main
  
  frame $menu -borderwidth 2 -relief raised
  pack $menu -fill x
  
# chaos-ed:mkmenus ...		;# done by chaos-ed:apply_mode
# chaos-ed:mkbuttons ...		;# done by chaos-ed:apply_mode
  chaos-ed:mkmain $main
  pack $main -expand yes -fill both
  
  if {[winfo class $window] == "Toplevel"} {
    wm title $window "No file"
    wm iconname $window "No file"
  }
}

######################################################################
# create text window with scrollbar
######################################################################

proc chaos-ed:mkmain { w } {
  chaos:debug
  global J_PREFS
  if {[lsearch [array names J_PREFS] {scrollbarside}] == -1} {
    set J_PREFS(scrollbarside) right ;# make sure it's defined
  }
  
  frame $w
  
  frame $w.status
  label $w.status.name -relief flat -text {(No file yet)}
  label $w.status.mode -relief flat -text "(unspecified)"
  scrollbar $w.s -relief flat -command "$w.t yview"
  # text widget is configured near end, after user's config file is read
  text $w.t -yscroll "$w.s set" -setgrid true
  
  pack $w.status.name -in $w.status -side left -fill x
  pack $w.status.mode -in $w.status -side right -fill x
  pack $w.status [chaos:rule $w] -in $w -side top -fill x
  pack $w.s [chaos:rule $w] -in $w -side $J_PREFS(scrollbarside) -fill y
  pack $w.t -in $w -side $J_PREFS(scrollbarside) -expand yes -fill both
  
  focus $w.t
  catch {focus default $w.t}		;# caught for Tk 4.0
  tk_bindForTraversal $w.t
  
  return $w
}

######################################################################
# create button bar
######################################################################

proc chaos-ed:mkbuttonbar { w t } {
  chaos:debug
  if [winfo exists $w] {
    destroy $w
  }
  
  frame $w
  
  set mode [chaos-ed:get_mode $t]
  
  if {"x[info procs mode:${mode}:mkbuttons]" != "x"} {
    mode:${mode}:mkbuttons $w.b $t
  } else {
    chaos:buttonbar $w.b -pady 2 -buttons [format {
      {done Done {chaos-ed:cmd:done %s}}
      {save Save {chaos-ed:cmd:save %s}}
      {load Load {chaos-ed:cmd:load %s}}
      {print Print {chaos-ed:cmd:print %s}}
    } $t $t $t $t]
  }
  pack $w.b [chaos:rule $w] -in $w -side top -fill x
  return $w
}

######################################################################
# set the label at the top of the window to current mode and filename
######################################################################

proc chaos-ed:set_label { window {title USE_FILENAME} } {
  chaos:debug
  chaos-ed:set_filename_label $window $title
  chaos-ed:set_mode_label $window [chaos-ed:get_mode $window]
}

######################################################################
# set the label at the top of the window to current filename
######################################################################

proc chaos-ed:set_filename_label { window {title USE_FILENAME} } {
  set file_label [chaos-ed:top_to_prefix $window].main.status.name
  
  set filename [chaos-ed:get_filename $window]
  if {"x$filename" == "x"} {
    set filename "No file"
  }
  
  if {$title == "USE_FILENAME"} then {set title [file tail $filename]}
  if {$title == "FULL_FILENAME"} then {set title $filename}
  
  if [winfo exists $file_label] {
    $file_label configure -text $title
  }
  
  if {[winfo class $window] == "Toplevel"} {
    wm title $window $title
    wm iconname $window $title
  }
}

######################################################################
# set the label at the top of the window to current mode
######################################################################

proc chaos-ed:set_mode_label { window {mode USE_MODE} } {
  if {$mode == "USE_MODE"} then {set mode [chaos-ed:get_mode $window]}
  
  set mode_label [chaos-ed:top_to_prefix $window].main.status.mode
  if [winfo exists $mode_label] {
    $mode_label configure -text [chaos-ed:get_mode $window]
  }
}

######################################################################
# position insert comfortably
######################################################################

proc chaos-ed:yview_insert {t} {
  set sb [chaos-ed:text_to_scrollbar $t]
  set insertline [lindex [split [$t index insert] .] 0]
  $t yview -pickplace {insert -5 lines}
  set lastline [lindex [$sb get] 3]		;# last visible line in $t
  if {$lastline >= $insertline} {
    $t yview -pickplace insert
  }
}


######################################################################
# set text for current preferences
######################################################################

proc chaos-ed:configure_text { t } {
  global CHAOS-ED_MODEPREFS CHAOS-ED_PREFS
  
  set mode [chaos-ed:get_mode $t]
  
  catch {$t configure \
    -background $CHAOS-ED_PREFS(textbg) \
    -foreground $CHAOS-ED_PREFS(textfg) \
    -insertbackground $CHAOS-ED_PREFS(textfg) \
    -selectbackground $CHAOS-ED_PREFS(textsb) \
    -selectforeground $CHAOS-ED_PREFS(textsf) \
    -selectborderwidth $CHAOS-ED_PREFS(textsbw) \
    -borderwidth $CHAOS-ED_PREFS(textbw) \
    -insertwidth $CHAOS-ED_PREFS(textiw) \
    -width $CHAOS-ED_MODEPREFS($mode,textwidth) \
    -height $CHAOS-ED_MODEPREFS($mode,textheight) \
    -wrap $CHAOS-ED_MODEPREFS($mode,textwrap)
  }
  chaos:configure_font $t $CHAOS-ED_MODEPREFS($mode,textfont) ;# knows about `default'
  # for rich-text:
  chaos-ed:font:configure_fonts $t
}

######################################################################
# various widget-name-guessing procedures
######################################################################

# .chaos-ed1.main.t -> .chaos-ed1

proc chaos-ed:text_to_top { t } {
  return [winfo parent [winfo parent $t]]
}

# .chaos-ed1.main.t -> .chaos-ed1.main.s

proc chaos-ed:text_to_scrollbar { t } {
  return "[winfo parent $t].s"
}

# .chaos-ed1.menu -> .chaos-ed1

proc chaos-ed:menubar_to_top { mb } {
  return [winfo parent $mb]
}

# .chaos-ed -> .chaos-ed, but "." -> ""

proc chaos-ed:top_to_prefix { top } {
  if {[string compare "." $top] == 0} {
    return ""
  } else {
    return $top
  }
}

# .chaos-ed -> .chaos-ed.main.t, but . -> .main.t

proc chaos-ed:top_to_text { top } {
  if {[string compare "." $top] == 0} {
    set prefix ""
  } else {
    set prefix $top
  }
  return ${prefix}.main.t
}

# .chaos-ed -> .chaos-ed.buttons, but . -> .buttons

proc chaos-ed:top_to_buttonbar { top } {
  if {[string compare "." $top] == 0} {
    set prefix ""
  } else {
    set prefix $top
  }
  return ${prefix}.buttons
}

# .chaos-ed -> .chaos-ed.menu, but . -> .menu

proc chaos-ed:top_to_menubar { top } {
  if {[string compare "." $top] == 0} {
    set prefix ""
  } else {
    set prefix $top
  }
  return ${prefix}.menu
}


