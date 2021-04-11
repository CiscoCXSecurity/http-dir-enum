#!/usr/bin/perl -w
# Crude little script to remove duplicates from the directories file.
#
# Features:
#
# - Retains original order
# - Retains comments and blank lines
# - Doesn't actually change file (writes to STDOUT)
# - Case sensitive
#
# Usage:
#
# dedup-dir-file.pl dirs.txt > new-dirs.txt
#
use strict;
my %seen;
my $comment_lines = 0;
my $line_lines = 0;
my $output_lines = 0;
my $blank_lines = 0;
my $removed_lines = 0;

while (<>) {
	chomp;
	my $line = $_;
	$line_lines++;
	if ($line =~ /^\s*$/) {
		print "$line\n"; # retain blank lines
		$blank_lines++;
		next;
	}
	if ($line =~ /^# /) {
		print "$line\n"; # retain comments
		$comment_lines++;
		next;
	}
	if ($seen{lc($line)}) {
		$removed_lines++;
	} else {
		print lc($line) . "\n";
		$output_lines++;
	}
	$seen{lc($line)} = 1;
}

warn "===========================\n";
warn "Lines processed: $line_lines\n";
warn "Lines retained:  " . ($output_lines + $blank_lines + $comment_lines) . "\n";
warn "Lines removed:   $removed_lines\n";
warn "Comment lines:   $comment_lines\n";
warn "Blank lines:     $blank_lines\n";
warn "===========================\n";
