#!/usr/bin/perl
#
# extract-doc.pl (name to be determined)
#
# convert embedded documentation to rst
# see pod for documentation
# 

use strict;
$^W = 1;

use Getopt::Long;
use Pod::Usage;
use File::Path;

# temporary for testing
#use Data::Dumper;

my $opt_help = 0;
my $opt_docprefix = ";d;";
my $opt_outputdir = "rst";
my $opt_outputext = ".rst";
my $opt_stripext = 1;
my $opt_overwrite = 1;

# we collect the documentation in docd
my %docd;

GetOptions(
  "docprefix=s"     => \$opt_docprefix,
  "outputdir=s"     => \$opt_outputdir,
  "outputext=s"     => \$opt_outputext,
  "stripext!"       => \$opt_stripext,
  "overwrite!"      => \$opt_overwrite,
  "help|?"          => \$opt_help,
) or pod2usage(1);

pod2usage(-exitstatus => 0, -verbose => 2) if $opt_help;

exit (&main());


sub main {
  $Data::Dumper::Indent = 1;
  $Data::Dumper::Sortkeys = 1;
  for my $f (@ARGV) {
    read_one_file($f);
  }
  write_out_files();
  #print Data::Dumper->Dump([\%docd], [qw(docdata)]);
  return 0;  
}

sub write_out_files {
  File::Path::make_path($opt_outputdir);
  for my $fn (keys %docd) {
    if (-r $fn && !$opt_overwrite) {
      die("Not overwriting file $fn, exit!");
    }
    open (OUT, ">$fn") or die("Cannot create file $fn: $!");
    # sort the priorities numerically
    for my $pr (sort {$a <=> $b} keys %{$docd{$fn}}) {
      for my $ss (sort keys %{$docd{$fn}{$pr}}) {
        for my $l (@{$docd{$fn}{$pr}{$ss}}) {
          printf OUT "$l\n";
        }
      }
    }
    close(OUT);
  }
}

sub read_one_file {
  my $fn = shift;
  open(IF, "<$fn") || die("Cannot open $fn: $!");
  my $current_output_file = compute_output_filename($fn);
  my $current_priority = 500;
  my $current_sortstring = "";
  while (<IF>) {
    chomp;
    if (m/^$opt_docprefix/) {
      my $dl = $_;
      $dl =~ s/^$opt_docprefix//;
      # if $dl is empty now, i.e., the line consisted *only* of
      # the docprefix, then we ship out an empty line
      if ($dl eq "") {
        push @{$docd{$current_output_file}{$current_priority}{$current_sortstring}}, "";
        next;
      }
      my $first_char = substr($dl, 0, 1);
      if ($first_char eq " ") {
        push @{$docd{$current_output_file}{$current_priority}{$current_sortstring}}, substr($dl, 1);
        next;
      } elsif ($first_char eq "=") {
        if ($dl =~ m!=file=([^\s]*)\s*$!) {
          $current_output_file = "$opt_outputdir/$1";
        } elsif ($dl =~ m!=priority=(\d*)!) {
          $current_priority = ($1 + 0);
        } elsif ($dl =~ m!=sortstring=(.*)$!) {
          $current_sortstring = $1;
        } else {
          printf STDERR "Unrecognized directive: >>$dl<< (file $fn)\n";
        }
      } else {
        printf STDERR "Unrecognized char after prefix: >>$first_char<< (file $fn)\n";
      }
    }
  }
}

sub compute_output_filename {
  my $path = shift;
  my $ret;
  # the following regexp works because of greedy matching in the first * op
  if ($path =~ m!(.*)/(.*)!) {
    $path = $2;
  }
  if ($opt_stripext) {
    $path =~ s!\.[^.]+$!!;
  }
  return "$opt_outputdir/$path$opt_outputext";
}

__END__

=head1 NAME

extract-doc - extract documentation from CL files (or any other)

=head1 SYNOPSIS

extract-doc [OPTION]... [FILE]...

=head1 OPTIONS

=over 4

=item B<--docprefix> I<regexp>

The regular expression I<regexp> is used to find lines in the input
files that correspond to documentation. 

Default: B<;d;>

=item B<--outputdir> I<dir>

Generated files are put into the directory I<dir>.

Default: B<rst>.

=item B<--no-stripext>

When computing the output file name, do not strip the last extension
from the file name. Default is to discard the last extension.

=item B<--no-overwrite> 

When generating output files, do not overwrite existing files.
The default is to overwrite existing files.

=item B<--help>

Gives this help page.

=back

=head1 DESCRIPTION

to be written

=head1 SPECIFICATION

Every line starting with

 	;d;

(or the value of B<--docprefix>)
is consider I<documentation input>.
 
The documentation generation routine has the concept of
current output file. By default it is the name of the
input file currently read. I.e., if the file

	foo.cl

is converted the default output file is named

 	foo.rst

The documentation conversion strips the last extension
(only 1) and adds rst. In case there is already a file
named like that, the translation process stops.
 
If the first character after the ";d;" of a documentation
line is a <SPACE>, i.e., the input line starts with

 	;d;<SPACE>

where <SPACE> is a literal space, then everything
following the <SPACE> is written into the current 
output file.
 
If the first char after the ";d;" is an "=", then
some directives for the translation mechanism 
can follow. Current directives are:

=over 4

=item	B<;d;=file=I<outputfile>>
changes the current output file

=item	B<;d;=priority=I<NN>>
 	  gives the following block a priority of NN

=item B<;d;=sortstring=I<STRING>>
 	  gives a sort string within this priority

=back

=head2 Output process

- all file given on the command line are read

- blocks with the same output file but different
   priority are written in increasing priority
   sequence.

- blocks within the same priority are sorted 
   according to the sortstring directive value
   (perl sort), meaning that empty sort string is
   sorted first.

- all block without specified priority get value 500
 

=head1 AUTHORS AND COPYRIGHT

This script and its documentation were written for the CafeOBJ system
(L<http://www.ldl.jaist.ac.jp/cafeobj/>), but may be used with arbitrary
other systems. Both are licensed under the GNU General Public License
Version 2 or later.

=cut

### Local Variables:
### perl-indent-level: 2
### tab-width: 2
### indent-tabs-mode: nil
### End:
# vim:set tabstop=2 expandtab: #
