#!/usr/bin/perl
#
# Copyright (c) 2014, Norbert Preining. All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
#
#   * Redistributions of source code must retain the above copyright
#     notice, this list of conditions and the following disclaimer.
#
#   * Redistributions in binary form must reproduce the above
#     copyright notice, this list of conditions and the following
#     disclaimer in the documentation and/or other materials
#     provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
# OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
# DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
# GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
# WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
# NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#

$^W=1;
use strict;

open IDX, ">wiki/index.mdwn" || die "Cannot create file wiki/index.mdwn: $!";

while (<>) { 
  chomp;

  if (m/^## (.*) ## \{#(.*)\}$/) {
    #print "found header $1 with target $2\n";
    close FOO;
    open FOO, ">wiki/$2.mdwn" || die "Cannot create file wiki/$2: $!";
    print FOO "## $1 ##\n";
    print IDX "- [$1](/wiki/$2)\n";
  } else {
    # we need to convert in-document links to urls
    print FOO necch($_), "\n";
  }
}
close IDX;

sub necch {
  my $a = shift;
  $a =~ s/\[([^]]*)\]\(#([^)]*)\)/[$1](\/wiki\/$2)/g;
  $a;
}

