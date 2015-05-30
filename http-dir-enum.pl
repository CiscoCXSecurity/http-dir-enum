#!/usr/bin/perl -w
# http-dir-enum - Enumerates Web Server directories using a word list
# Copyright (C) 2006 Mark Lowe ( mrl@portcullis-security.com )
# 
# Disclaimers
#
# This tool may be used for legal purposes only.  Users take full 
# responsibility for any actions performed using this tool.
# http-dir-enum comes with ABSOLUTELY NO WARRANTY;
# If these terms are not acceptable to you, then do not use this tool.
#
# License
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License version 2 as 
# published by the Free Software Foundation provided the clauses
# in the disclaimer section above are adhered to.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public License along
# with this program; if not, write to the Free Software Foundation, Inc.,
# 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
#
# This tool may be used for legal purposes only.  Users take full
# responsibility for any actions performed using this tool.  If these terms are
# not acceptable to you, then do not use this tool.
# 
# You are encouraged to send comments, improvements or suggestions 
# and new word lists to me at mrl@portcullis-security.com
#
# Credits
#
# This program is derived from dns-grind ( http://pentestmonkey.net/tools/dns-grind )
# Inspiration is largely drawn from dirBuster ( http://www.sittinglittleduck.com/dirBuster/ )
#
# Bugs / missing features
# 
# * Need to read in a list of directories.  This can be useful if you need to rescan 
#   the whole directory structure for a file/dir you weren't looking for when you 
#   did the first scan.
#   
# * For each new directory found, parse the links out of that page.  It will probably
#   only work well for 200 responses, but we'll do all response codes for completeness.
#   This saves you having to stop the script and restart it with a slightly altered dir 
#   list.  Kind of a spider-bruteforce hybrid.
#
# * Manually exclude directories, e.g. process http://host/, but exclude http://host/other-app/
#
# * When we get a directory listing (e.g. from apache), it's obvious what the
#   sub dirs are.  There should be an option to avoid brute-forcing subdirs
#   when dir listings are available and just follow the directory links.
#
# * GET requests sometimes cause warning messages about UTF-8 encoding in the
#   underlying LWP module.
#
# * Some sort of indication of scan rate / ETA would be helpful
#
# * Option to check for files.  Workaround is -f files.txt -s 0 -r 0.
#
# * Save responses.  Maybe had an option to include them in the XML output.
#
# * Check site is actually reachable before scanning!
#
# * Add support for multiple cookies
#
# * dynamically add more processes?
#
# * Option to ignore based on regexp of whole reply (incase custom error pages
#   are used which are send with 200 OK status)
#
# * Add support for client SSL certs
#
# * It'd be useful to characterise error messages (maybe by hashing the response).
#   Sometimes two different directories will both return 404 messages for non-
#   existent pages, but the text of the messages are very different.  It's handy
#   to know this, particulalry when testing weblogic which seems to return a 404
#   that's vulnerable to xss for certain file extensions.
#

use strict;
use Data::Dumper;
use Socket;
use LWP;
use Carp;
use IO::Handle;
use IO::Select;
use Getopt::Std;
use XML::Simple;
use MIME::Base64;
$| = 1;

my $VERSION            = "0.4.3";
my $global_debug       = 0;
my $global_verbose     = 0;
my $username           = undef;
my $password           = undef;
my $max_procs          = 8;
my $recursive_flag     = 1;
my $query_timeout      = 20;     # some active content takes ages to load
my $http_method        = "head"; # lowercase - it's a method name
my $trailing_slash     = 1;
my $dir_lines          = undef;
my $global_slash       = '/';
my $auto_detect_ignore = 1;
my $close_connection   = 0;
my $global_ignore_code = undef;
my $max_scan_rate      = undef;
my $use_cookie         = undef;
my $dump_code          = undef;
my $proxy_url          = undef;
my $output_file        = undef;
my $follow_redirects   = 0;
my $global_quiet       = 0;
my $start_time         = time();
my $user_agent_string  = 'Mozilla/5.0 (X11; U; Linux i686; en-US; rv:1.8.1.2) Gecko/20070318 Firefox/2.0.0.2';
my $kill_child_string  = "\x00";
my $case_sensitive_dirs = 1;
my @dirs_found = ("/");
my $http_opt;
my $end_time;
my %global_results = ();
my @child_handles      = ();
$SIG{CHLD} = 'IGNORE'; # auto-reap
my %opts;
my $usage=<<USAGE;
http-dir-enum v$VERSION ( http://labs.portcullis.co.uk/application/http-dir-enum/ )
Copyright (C) 2006 Mark Lowe ( mrl\@portcullis-security.com )

Given a URL and a wordlist, http-dir-enum will attempt to determine names of
directories that exist on a website.

Usage: http-dir-enum.pl [options] -f dir-file url

options are:
        -m n     Maximum number of worker processes (default: $max_procs)
	-f file  File of potential directory names
	-k file  File of known directory names
	-c 0|1   Close connection between each attempt (default: $close_connection)
	-r 0|1   Recursively enumerate sub directories (default: $recursive_flag)
	-t n     Wait a maximum of n seconds for reply (default: $query_timeout)
	-u user  Username to use for basic authentication
	-p pass  Password to use for basic authentication
	-H g|h   HTTP method g=GET, h=HEAD (default: $http_method)
	-i code  Ignore HTTP response code (e.g. 404 or '404|200')
	-U str   Set User-Agent header to str (default based on Firefox 2.0.0.2/Linux)
	-s 0|1   Add a trailing slash to the URL (default: $trailing_slash)
	-S 0|1   Case sensitive directory names (default: $case_sensitive_dirs)
	-a 0|1   Automatically determine HTTP response code to ignore (default: $auto_detect_ignore)
	-l n     Limit scan to n attempts per second (default: unlimited)
	-R 0|1   Follow redirects (default: $follow_redirects)
	-q       Quiet.  Don't print out info (\"[I]\") messages
	-n n     Only read first n lines of dirs file (default: unlimited)
	-o file  Save XML report of dirs found to file (default: don't save a report)
	-x regx  Return only results that match this regular expression
	-X regx  Ignore results that match this regular expression
	-P url   Proxy URL
	-C str   Use cookie
	-v       Verbose
	-d       Debugging output
	-D code  Print out whole response if it has HTTP code \"code\" (e.g. 500)
	-h       This help message

The default options should be suitable most of the time, so the
typical usage would be:

http-dir-enum.pl -f dirs.txt http://host

PERFORMANCE TIPS:

* Make sure the number of processes (-m) is less than the number of directories
  passed via the -f option.  It normally is anyway.

* Use a lower number of processes (e.g. 2) over fast connections like localhost.  Use a 
  higher number (e.g. 8 or 32) over laggy connections.

USAGE

getopts('m:f:c:r:t:u:p:H:i:U:s:vdha:l:R:qC:n:P:D:o:S:k:x:X:', \%opts);

# Print help message if required
if ($opts{'h'}) {
	print $usage;
	exit 0;
}

# Single non-option is URL
my $url         = shift or die $usage;

# Process options
$max_procs         = $opts{'m'} if $opts{'m'};
my $file           = $opts{'f'} if $opts{'f'};
my $known_dir_file = $opts{'k'} if $opts{'k'};
$close_connection  = $opts{'c'} if defined($opts{'c'}) and ($opts{'c'} == 1 or $opts{'c'} == 0);
$recursive_flag    = $opts{'r'} if defined($opts{'r'}) and ($opts{'r'} == 1 or $opts{'r'} == 0);
$query_timeout     = $opts{'t'} if $opts{'t'};
$username          = $opts{'u'} if $opts{'u'};
$password          = $opts{'p'} if $opts{'p'};
$http_opt          = $opts{'H'} if $opts{'H'};
my $match_pattern     = $opts{'x'} if $opts{'x'};
my $dont_match_pattern = $opts{'X'} if $opts{'X'};
$global_ignore_code       = $opts{'i'} if $opts{'i'};
$user_agent_string = $opts{'U'} if $opts{'R'};
$trailing_slash    = $opts{'s'} if defined($opts{'s'}) and ($opts{'s'} == 1 or $opts{'s'} == 0);
$case_sensitive_dirs      = $opts{'S'} if defined($opts{'S'}) and ($opts{'S'} == 1 or $opts{'S'} == 0);
$global_verbose           = $opts{'v'} if $opts{'v'};
$global_debug             = $opts{'d'} if $opts{'d'};
$auto_detect_ignore       = $opts{'a'} if defined($opts{'a'}) and ($opts{'a'} == 1 or $opts{'a'} == 0);
$max_scan_rate            = $opts{'l'} if defined($opts{'l'});
$follow_redirects         = $opts{'R'} if defined($opts{'R'}) and ($opts{'R'} == 1 or $opts{'R'} == 0);
$use_cookie               = $opts{'C'} if defined($opts{'C'});
$dir_lines                = $opts{'n'} if defined($opts{'n'});
$proxy_url                = $opts{'P'} if defined($opts{'P'});
$dump_code                = $opts{'D'} if defined($opts{'D'});
$output_file              = $opts{'o'} if defined($opts{'o'});
$global_quiet             = 1 if defined($opts{'q'});

# Check input file was provided
unless ($file) {
	print $usage;
	exit 1;
}

# Check output file is writable
if (defined($output_file)) {
	unless (open(OUTFILE, ">$output_file")) {
		print "ERROR: Can't open output file $output_file for writing: $!\n";
		exit 1;
	}
}

# Check known dir file is read, read in dirs
if (defined($known_dir_file)) {
	unless (open(DIRFILE, "<$known_dir_file")) {
		print "ERROR: Can't open known dir file $known_dir_file for reading: $!\n";
		exit 1;
	}

	# Populate the dirs_found array
	@dirs_found = ();
	while (<DIRFILE>) {
		chomp;
		my $line = $_;
		push @dirs_found, $line;
	}

	# Don't let dirs_found be empty
	unless (@dirs_found) {
		@dirs_found = ('/');
	}
}

# Check HTTP method is valid
if (defined($http_opt)) {
	my $correct_option = 0;

	if ($http_opt =~ /^h/i) {
		$correct_option = 1;
		$http_method = "head";
	}

	if ($http_opt =~ /^g/i) {
		$correct_option = 1;
		$http_method = "get";
	}

	unless ($correct_option) {
		print "ERROR: Invalid option passed via -H.  Should be g (for GET) or h (for HEAD)\n";
		exit 1;
	}
}

print "Starting http-dir-enum v$VERSION ( http://labs.portcullis.co.uk/application/http-dir-enum/ )\n";
print "Copyright (C) 2006 Mark Lowe ( mrl\@portcullis-security.com )\n";
print "\n";
print " ----------------------------------------------------------\n";
print "|                   Scan Information                       |\n";
print " ----------------------------------------------------------\n";
print "\n";
print "URL .................... $url\n";
print "Processes .............. $max_procs\n";
print "Directory name file .... $file\n" if defined($file);
print "Query timeout .......... $query_timeout secs\n";
print "Basic username ......... $username\n" if defined($username);
print "Basic password ......... $password\n" if defined($password);
print "HTTP Method ............ " . uc($http_method) . "\n";
print "Max Queries / sec ...... " . (defined($max_scan_rate) ? $max_scan_rate : "unlimited") . "\n";
print "Use cookies ............ " . "$use_cookie\n" if defined($use_cookie);
print "Trailing slash ......... " . ($trailing_slash ? "On" : "Off") . "\n";
print "Recursive dir search ... " . ($recursive_flag ? "On" : "Off") . "\n";
print "Close connections ...... " . ($close_connection ? "On" : "Off") . "\n";
print "Follow redirects ....... " . ($follow_redirects ? "On" : "Off") . "\n";
print "Case sensistive dirs ... " . ($case_sensitive_dirs ? "On" : "Off") . "\n";
print "Auto-ignore ............ " . ($auto_detect_ignore ? "On" : "Off") . "\n";
if (defined($output_file)) {
	print "Output file ............ $output_file\n";
}
if (defined($proxy_url)) {
	print "Proxy .................. $proxy_url\n";
}
if (defined($global_ignore_code)) {
	print "Ignore ................. $global_ignore_code\n";
}

print "\n";
print "######## Scan started on " . scalar(localtime()) . " #########\n";

# We make our own specialization of LWP::UserAgent that asks for
# user/password if document is protected.
no warnings;
sub LWP::UserAgent::get_basic_credentials {
	my($self, $realm, $uri) = @_;
	return ($username, $password);
}
use warnings;

no warnings;
sub LWP::UserAgent::redirect_ok {
	if ($follow_redirects) {
		return 1;
	} else {
		return 0;
	}
}
use warnings;

if ($trailing_slash) {
	$global_slash = '/';
} else {
	$global_slash = '';
}

# Create HTTP client
my $ua;
if ($close_connection) {
	$ua = LWP::UserAgent->new(timeout => $query_timeout);
} else {
	$ua = LWP::UserAgent->new(timeout => $query_timeout, keep_alive => 1);
}
$ua->agent($user_agent_string);

if (defined($use_cookie)) {
	$ua->default_header("Cookie" => $use_cookie);
}

if (defined($proxy_url)) {
	$ua->proxy(['http', 'https'], $proxy_url);
}

# determine which HTTP response code we should ignore
my %global_auto_ignore_code = ();

# Spawn off correct number of worker processes
foreach my $proc_count (1..$max_procs) {
	socketpair(my $child, my $parent, AF_UNIX, SOCK_STREAM, PF_UNSPEC) or  die "socketpair: $!";
	$child->autoflush(1);
	$parent->autoflush(1);

	# Parent executes this
	if (my $pid = fork) {
		close $parent;
		print "[Parent] Spawned child with PID $pid to do directory name guessing\n" if $global_debug;
		push @child_handles, $child;

	# Child executes this
	} else {
		close $child;

		while (1) {
			my $timed_out = 0;
			my $query_successful = 0;
			my $timeout_message = "Query timed out\n";

			# Read dir from parent
			my $dir = <$parent>;
			next unless defined($dir);
			chomp($dir);
			my $url_with_dir = "$url/$dir$global_slash";

			# Exit if told to by parent
			if ($dir eq $kill_child_string) {
				print "[Child $$] Exiting\n" if $global_debug;
				exit 0;
			}
			
			my $trace;
			if ($global_debug) {
				$trace = "[Child $$] $dir\t";
			} else {
				$trace = "$dir\t";
			}

			# Do query with timeout (timeout implemented by LWP, so no need for alarms)
			# Keep doing it until we don't time out
			my $response;
			while (!$query_successful) {
				$response = $ua->$http_method($url_with_dir);
	
				if ($response->status_line =~ /500 read timeout/) {
					print "[Child $$] Timeout for directory \"$dir\".  Retrying...\n" if $global_debug;
				} else {
					$query_successful = 1;
				} 
			}

			if ($response) {
				if (defined($dump_code) and $response->code =~ /$dump_code/) {
					print $response->as_string;
				}
				if (defined($match_pattern) or defined($dont_match_pattern)) {
					print $parent $trace . $response->code . "\t" . encode_base64($response->as_string, "") . "\n";
				} else {
					print $parent $trace . $response->code . "\n";
				}
			} else {
				print "$trace ERROR no response from HTTP query!\n";
				print $parent $trace . "<no response>\n";
			}

		}
		exit;
	}
}

my $s = IO::Select->new();
my $s_in = IO::Select->new();
$s->add(@child_handles);
$s_in->add(\*STDIN);
my $timeout = 0; # non-blocking
my $more_dirs = 1;
my $outstanding_queries = 0;
my $query_count = 0;
my $result_count = 0;
my $get_next_dir;
my $worker_queue_length = 1;

my $more_work = 1;

while ($more_work or scalar @dirs_found) {
	
	my $subdir = new_subdir();

	for (1..$worker_queue_length) {

		# Write to each child process once
		writeloop: foreach my $write_handle (@child_handles) {
			print "[Parent] Writeloop: Outstanding queries: $outstanding_queries\n" if $global_debug;
			my $dir = <$get_next_dir>;
			unless ($dir) {
				unless ($subdir = new_subdir()) {
					print "[D] Quitting Writeloop.  All dirs have been read.\n" if $global_debug;
					$more_work = 0;
					last writeloop;
				}
	
				# $get_next_dir is reinitialised now
				$dir = <$get_next_dir>;
			}
	
			chomp($dir);
			$dir = "$subdir/$dir";
			$dir =~ s/^\///; # strip off leading /
			print "[Parent] Sending $dir to child\n" if $global_debug;
			print $write_handle "$dir\n";
			$outstanding_queries++;
	
		}
	}

	print "[Parent] Writeloop complete.  Starting Mainloop.\n" if $global_debug;
	
	# Keep reading from child processes until there is nothing
	# write to a child only after it has been read from
	mainloop: while ($more_work) {
		print "[Parent] Mainloop: Outstanding queries: $outstanding_queries\n" if $global_debug;

		# Wait until there's a child that we can either read from or written to.
		my ($rh_aref) = IO::Select->select($s, undef, undef); # blocking
	
		print "[Parent] There are " . scalar(@$rh_aref) . " children that can be read from\n" if $global_debug;
	
		foreach my $read_handle (@$rh_aref) {

			# Wait until we're below our scan-rate target
			while (defined($max_scan_rate) and get_scan_rate() > $max_scan_rate) {
				select(undef, undef, undef, 0.1);
			}
	
			# Read from child
			chomp(my $line = <$read_handle>);
			my $dir_found = process_result($line);
			if (defined($dir_found)) {
				print "[Parent] Found directory: $dir_found\n" if $global_debug;
				$result_count++;
				push @dirs_found, $dir_found if $recursive_flag;
				print Dumper \@dirs_found if $global_debug;
			}
			$outstanding_queries--;
			$query_count++;
	
			# Write to child
			my $dir = <$get_next_dir>;
			unless ($dir) {
				unless ($subdir = new_subdir()) {
					print "[D] Quitting Mainloop.  All dirs have been read.\n" if $global_debug;
					$more_work = 0;
					last mainloop;
				}

				# get_next_dir is reinitialise now
				$dir = <$get_next_dir>;
			}
			chomp($dir);
			$dir = "$subdir/$dir";
			$dir =~ s/^\///; # strip off leading /
			print "[Parent] Sending $dir to child\n" if $global_debug;
			print $read_handle "$dir\n";
			$outstanding_queries++;
		}
	}
	
	print "[Parent] Mainloop complete.  Starting Readloop.\n" if $global_debug;
	
	# Wait to get replies back from remaining children
	# It's a slow process waiting for all the results to come back but we need to
	# it incase some more dirs are found.  If more dirs are found, we'll go and do the write and mail loop again
	my $count = 0;
	readloop: while ($outstanding_queries) {
		print "[Parent] Readloop: Outstanding queries: $outstanding_queries\n" if $global_debug;
		my @ready_to_read = $s->can_read(1); # blocking
		foreach my $child_handle (@ready_to_read) {
			print "[Parent] Outstanding queries: $outstanding_queries\n" if $global_debug;
			chomp(my $line = <$child_handle>);
			my $dir_found = process_result($line);
			if (defined($dir_found)) {
				print "[Parent] Found directory: $dir_found\n" if $global_debug;
				$result_count++;
				push @dirs_found, $dir_found if $recursive_flag;
				print Dumper \@dirs_found if $global_debug;
			}

			$outstanding_queries--;
			$query_count++;
		}
	}

	print "[Parent] Readloop complete.  Subdirs remaining:\n" if $global_debug;
	print Dumper \@dirs_found if $global_debug;
}

print "[Parent] Killing worker processes\n" if $global_debug;

# Tell any remaining children to exit
foreach my $handle ($s->handles) {
	print "[Parent] Telling child to exit\n" if $global_debug;
	print $handle "$kill_child_string\n";
	$s->remove($handle);
}

# Wait for all children to terminate
while(wait != -1) {};

print "######## Scan completed on " . scalar(localtime()) . " #########\n";

print "$result_count results.\n";
print "\n";
$end_time = time(); # Second granularity only to avoid depending on hires time module
my $run_time = $end_time - $start_time;
$run_time = 1 if $run_time < 1; # Avoid divide by zero
my $scan_rate = get_scan_rate();
printf "%d queries in %d seconds (%0.0f queries / sec)\n", $query_count, $run_time, $scan_rate;

if (defined($output_file)) {
	my %opts;
	$opts{version} = $VERSION;
	$opts{end_time} = $end_time;
	$opts{start_time} = $start_time;
	$opts{end_time_string} = scalar(localtime($end_time));
	$opts{start_time_string} = scalar(localtime($start_time));
	$opts{starturl} = $url;
	$opts{processes} = $max_procs;
	$opts{dirsfile} = $file;
	$opts{timeout} = $query_timeout;
	$opts{username} = defined($username) ? $username : "[not_set]";
	$opts{password} = defined($password) ? $password: "[not_set]";
	$opts{http_method} = $http_method;
	$opts{scan_rate} = defined($max_scan_rate) ? $max_scan_rate : "unlimited";
	$opts{cookie} = defined($use_cookie) ? $use_cookie : "[not_set]";
	$opts{trailing_slash} = $trailing_slash ? "On" : "Off";
	$opts{recursive} = $recursive_flag ? "On" : "Off";
	$opts{close_connection} = $close_connection ? "On" : "Off";
	$opts{follow_redirects} = $follow_redirects ? "On" : "Off";
	$opts{auto_detect_ignore} = $auto_detect_ignore ? "On" : "Off";
	$opts{proxy} = defined($proxy_url) ? $proxy_url : "None";
	$opts{ignore_code} = defined($global_ignore_code) ? $global_ignore_code : "[not_set]";

	for my $key (keys %opts) {
		$global_results{scan_options}{$key} = { value => $opts{$key}};
	}

	my $xml = XMLout(\%global_results);
	print OUTFILE $xml;
	print "XML report saved to $output_file\n";
}


###################
# Subs below here #
###################

sub get_scan_rate {
	$end_time = time(); # Second granularity only to avoid depending on hires time module
	my $run_time = $end_time - $start_time;
	$run_time = 1 if $run_time < 1; # Avoid divide by zero
	return $query_count / $run_time;
}

# process_result is called by partent to determine if the string
#                returned by worker process is a positive result
#                Prints result to STDOUT as appropriate
#
# args:    single string passed back from worker process
# returns: directory name if positive result, undef if not
sub process_result {
	my ($line) = @_;
	my $result_count = 0;
	my $error_response = 0;
	my $debug_or_verbose = 0;
	my $ignore = 0;
	# my ($dir, $code) = $line =~ /^(?:\[Child \d+\]\s+)?([^\t]+)\t(\d+)/;
	# print $line;
	my ($dir, $code, $response_base64) = $line =~ /^(?:\[Child \d+\]\s+)?([^\t]+)\t(\d+)(?:\s+([A-Za-z0-9=\/+]*))?/;
	# print "dir: $dir, code: $code, response: $response_base64\n";
	my $gaic;
	my $subdir;
	if (defined($dir)) {
		($subdir) = $dir =~ /^([^\t]+)\//;
		$subdir = '' unless defined($subdir);
		$gaic = $global_auto_ignore_code{$subdir};
	}

	my $response_string = "";
	if (defined($response_base64)) {
		$response_string = decode_base64($response_base64);
	}

	$error_response   = 1 if ($line =~ /[^\t]+\t.*result/ or $line =~ /[^\t]+\t.*<timeout>/);
	$debug_or_verbose = 1 if ($global_verbose == 1 or $global_debug == 1);
	$ignore           = 1 if (
					(defined($global_ignore_code) and $line =~ /\t$global_ignore_code$/) or
					(defined($gaic) and $line =~ /\t$gaic$/) or
					(defined($match_pattern) and defined($response_base64) and $response_string !~ /$match_pattern/) or
					(defined($dont_match_pattern) and defined($response_base64) and $response_string =~ /$dont_match_pattern/)
				);

	# if the response is interesting print it out
	if ($debug_or_verbose or not $ignore) {
		# Check if it's a duplicate
		if (defined($global_results{dirs_found}{$dir}) or (!$case_sensitive_dirs and defined($global_results{dirs_found}{lc($dir)}))) {
			return undef;
		} else {
			print "$dir\t$code\n";
		}
		if (not $ignore and not $error_response) {
			if ($case_sensitive_dirs) {
				$global_results{dirs_found}{lc($dir)} = { code => $code }; # TODO store more stuff in hash (e.g. HTTP response)
			} else {
				$global_results{dirs_found}{$dir} = { code => $code }; # TODO store more stuff in hash (e.g. HTTP response)
			}
			return $dir;
		}
	}

	return undef;
}

# Returns a string which we presume won't be present on the server
# TODO randomly generate this?
sub non_existant_dir {
	return "doesntexist";
}

sub restart_dir_generator {
	print "[Directory Generator] (re)Starting\n" if $global_debug;
	# Fork once more to make a process that will feed us dirs
	socketpair($get_next_dir, my $parent, AF_UNIX, SOCK_STREAM, PF_UNSPEC) or  die "socketpair: $!";
	$get_next_dir->autoflush(1);
	$parent->autoflush(1);
	
	# Parent executes this
	if (my $pid = fork) {
		close $parent;
		return $get_next_dir;
	
	# Child executes this
	} else {
		# Read dirs from file and send to parent
		open (FILE, "<$file") or die "Can't open file $file: $!\n";
		my $dir_count = 0;
	
		while (<FILE>) {
			my $dir = $_;
			$dir =~ s/\x0d//g; # pesky DOS text files
			chomp($dir);
			next if $dir =~ /^# /; # allow comments in dirs file
			next if $dir =~/^\s*$/; # ignore lines of white space
			$dir_count++;
			print "[Directory Generator] Sending dir #$dir_count \"$dir\" to parent\n" if $global_debug;
			if ($case_sensitive_dirs) {
				print $parent "$dir\n";
			} else {
				print $parent lc($dir) . "\n";
			}
			if (defined($dir_lines) and $dir_count >= $dir_lines) {
				print "[Directory Generator] Reached maximum read count passed via -n: $.\n" if $global_debug;
				last;
			}
		}

		print "[Directory Generator] Exiting\n" if $global_debug;;
	
		exit 0;
	}
}

sub update_auto_ignore {
	my $url = shift;
	my $subdir = shift;
	$url = "$url/$subdir";
	$url =~ s/\/$//; # strip trailing slash
	if ($auto_detect_ignore) {
		# Request non-existant file
		my $response = $ua->$http_method("$url/" . non_existant_dir() . $global_slash);
	
		$global_auto_ignore_code{$subdir} = $response->code;
		print "[I] Auto-ignoring HTTP code " . $global_auto_ignore_code{$subdir} . " for $url\n" unless $global_quiet;
	}
}

sub new_subdir {
	my $subdir = shift @dirs_found;
	if (defined($subdir)) {
		$get_next_dir = restart_dir_generator();
		print "[I] Processing directory: $subdir (" . (scalar @dirs_found) . " dirs remaining)\n" unless $global_quiet;
		$subdir =~ s/^\/+//; # strip off leading /
		update_auto_ignore($url, $subdir);
		return $subdir;
	} else {
		return undef;
	}
}

