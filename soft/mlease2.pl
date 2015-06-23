#!/usr/bin/perl
#use IO::Interface qw(:flags);
#use IO::Socket::INET;
#use Proc::PID_File;
#use Tie::FileHandle::Base;
#use Tie::FileHandle::MultiPlex;
#use Time::HiRes qw(gettimeofday sleep);
#use XML::Simple;

#########################################
#
# New version revised by belzey
#
# Based off version 1.4.1 by mdettinger
# revised by belzey
# 10/26/2009
# ver: 2.2.0
#
#########################################
use IO::Socket;
use IO::Select;
use strict;

# Global Variable for Version
my $version="2.2.0";

# Unbuffered output
$|=1;

# global variables
my $pidFile;                      # PID File filename
my $psock;                        # Primary DHCP Sending Socket
my $bsock;                        # Broadcast listening Socket
my $server="255.255.255.255";     # Primary DHCP Address
my $dualserver="";                # Dual Nic DHCP Address     
my $expected_server="";           # Only process response from this server
my $splitserver="";               # Split Scope or Rogue DHCP Server
my $foserver="";                  # Secondary DHCP Address
my @serverArray="255.255.255.255";# Array of servers that should receive packets.
my $local=68;                     # use this local port 
                                  #   valid DHCP values (67,68)
my $specificInterface;            # Use a specific interface on a multiNIC box.
my $discs=1;                      # Number of test hardware addresses 
my $numberOfMsgBunch=25;          # Number of msg to send before 
                                  #   collecting responses.
my $timeOutGiveUp=2;              # Number of consecutive timeouts
                                  #   before test is terminated
my $timeOutWaiting=.5;            # Time required to time out 
                                  #   the listening port
my $reDiscoverTimeOuts=0;         # Retry packets that timed out waiting 
                                  #   for response.
my $reDiscTimeOutsMaxTries=1000;  # The total number of time outs before
                                  #   Rediscovering is terminated.
my $waitCluster=0;                # Delay before starting next cluster
my $waitTrial=0;                  # Delay before starting next trial
my $initialType="DHCP DISCOVER";  # Initial DHCP message type
my $sendOnly=0;                   # Do not wait for server Response
                                  ### $xid trigger = fffffxxx
my @dhcppacket;                   # Array containing DHCP packet
                                  #   information - possible to 
                                  #   localize in future release 
my @detailpacket;                   # Array containing DHCP packet
                                  #   information - more than
                                  #   in dhcppacket array
my $hw_addr_length=6;             # Length of the hardware address 
                                  #   valid values (6-16)
my $ciaddr=INADDR_ANY;            # Value of CIADDR
my $yiaddr=INADDR_ANY;            # Value of YIADDR
my $siaddr=INADDR_ANY;            # Value of SIADDR
my $giaddr=INADDR_ANY;            # Value of GIADDR
my $ch_prefix="0fffff";           # Default client harware address
                                  #   prefix 
my $ch_suffix="000001";           # Default client harware address
                                  #   suffix
my $chaddr="";                    # Default client harware address
                                  #   (prefix + suffix)
my $sName="0";			          # Server Name
my $bootFile="0";		          # Bootfile
my $magicCookie="63825363";       # Default magic cookie
my $optionsToSend;                # Scalar options varable
my $options="";                   # DHCP options as a hex stream
my %clientOptions;                # Hwaddr-clientside options hash table
my %serverOptions;                # HWaddr-server sent options hash table
my $hostname="dhcp-client";       # Default DHCP client name.
my $opt15="";                     # Client provided domain name
my $opt40="";			          # NIS Domain.
my $opt43="";                     # Client Vendor Specific Options
my $opt50="";                     # Client requested IP address
my $opt51="";                     # Client requested lease time
my $opt52;                        # Option overload
my $opt54="";			          # User specified Server option for renews.
my $opt55="";                     # Client requested options list
my $opt60="";                     # Client provided Vendor Class
my $phone="";                     # Option 61 as a phone number.
my $opt77="";                     # Client provided User Class
my $opt80="";                     # Rapid Commit Option
my $incHostname=1;                # Loop control variable to increment Hostname
my $fqdn_hostname="";             # Option 81 fqdn
my $fqdn_domain="";               # Option 81 temporary storage variable
my $opt81flag="";		          # Option 81 format flag
my $opt81Long="";                 # Use Long Option Support for Option 81
my $opt82="";                     # Relay Agent Option.
my $o82="";                       # Temp var 
my $o82len="";			          # Length of Option 82.
my $o82_1="";                     # Value for Option 82 Suboption 1
my $o82_2="";			          # Value for Option 82 Suboption 2
my $o82_4=0;                      # Value for Option 82 Suboption 4
my $o82_5="";			          # Value for Option 82 Suboption 5
my $o82_6="";                     # Value for Option 82 Suboption 6
my $o82_9="";			          # Value for Option 82 Suboption 9
my $o82_11="";                    # Value for Option 82 Suboption 11
my $opt118="";                    # Client subnet selection option
my $opt250="";			          # User Defined Option 250
my $opt250long="";                # Concatinate Option 250
my $optionTerminator="ff";        # DHCP option terminator
my $decodeOptionsServerPacket;    # Decode options from server packets
my $dhcpLeaseQueryType="mac";     # DHCP LEASE QUERY message query type
                                  #   values = ip, mac, id
my @with=();                      # fussy client required options
my @without=();                   # fussy client prohibited options
my $renewGiaddr=1;                # Use GIAddr for renews.
my $renewN=1;     # Counter for the number of REQUESTS to be made after DORA
my $renew=0;      # 1 - renew after DORA;	2-renew after @agenda
                  ###   $xid trigger = bbbb?xxx
my $decline=0;    # 1 - decline after DORA;
                  # 3 - discover after decline;
                  ###   $xid trigger = dddd?xxx 
my $nack=3;       # 3 - discover after NACK;
my $release=0;    # 1 - release after DORA;     2 - release after @agenda;
                  # 3 - discover after release; 
                  # 4 - release now discover after @agenda; 
                  # 5 - discover after release after @agenda
my $releaseN=1;   # Default number of release attempts.
                  ###   $xid trigger = eeee?xxx 
my $inform=0;     # Counter for the number of informs to perform.
my @agenda;       # Master Lists of all tasks.
my $inFile="";    # The input file to populate @agenda
my @toDoList;     # Subset of @agenda that the main loop will process
my @actionItems;  # Loose ends from @toDoList that the main loop will 
                  #   process before taking another chunk of @agenda
my $outerLoop=1;  # Number of times to run test battery
my $discount=0; my $totalDisCount=0;                 # Global counter
my $offcount=0; my $totalOffCount=0;                 # Global counter
my $reqcount=0; my $totalReqCount=0;                 # Global counter
my $deccount=0; my $totalDecCount=0;                 # Global counter
my $ackcount=0; my $totalAckCount=0;                 # Global counter
my $nakcount=0; my $totalNakCount=0;                 # Global counter
my $relcount=0; my $totalRelCount=0;                 # Global counter
my $infcount=0; my $totalInfCount=0;                 # Global counter
my $lqcount=0; my $totalLqCount=0;                   # Global counter
my $lqunkcount=0; my $totalLqunkCount=0;             # Global counter
my $lqunacount=0; my $totalLqunaCount=0;             # Global counter
my $lqactcount=0; my $totalLqactCount=0;             # Global counter
my $bootpRequest=0; my $totalBpReqCount=0;           # Global counter
my $bootpReply=0;   my $totalBpRepCount=0;           # Global counter
my $timeOutCounter=0;   my $totalTimeOutCount=0;     # Number of packets timed out
my $badPacketCounter=0; my $totalBadPacketCount=0;   # Number of Bad Packets
my $ignoredPacketCounter=0; my $totalIgnoreCount=0;  # Number of Ignored Packets
my $unexpectedPacketCounter=0; my $totalUnexCount=0; # Number of Unexpected Packets
my $logfile="";            	 	# Logfile
my $fileLogging=2;         		# Logging level to a file
my $screenLogging=0;       		# Logging level to the screen
my $outputSuppressionFactor=1;		# The number of trials to supress from logging
my $progressBar=0;         		# State of on-screen progress bar
my $totalTrialTime=0;      		# Total Time across all clusters in trial
my $totalRunTime=0;        		# Total Time across all trials


## Disclaimer
#############
my $disclaimer = "Copyright 2009,  Alcatel-Lucent (for internal, use only)";


## Subroutine to show this script's version.
############################################
sub version {
  print "$0 version $version\n";
  print "      $disclaimer\n";
  exit;
}


## Subroutine to determine the IP address of this station.
##########################################################
sub myIP {
  chomp(my $client_hostname = `hostname`);
  (my $Proto_name,my $Proto_aliases,my $type,my $len,my $ip_local) =
	gethostbyname($client_hostname);
  $ip_local = inet_ntoa($ip_local);
  return $ip_local;
}


## Subroutine to configure port to accept unicasted DHCP traffic.
#################################################################
sub setupSocket {
    my $ip_local = shift;
  
	if ($ip_local eq "127.0.0.1") {
		print STDOUT "hostname is not defined\n";
	}
  	$psock = IO::Socket::INET->new( 
            LocalPort => $local,
	    LocalAddr => $ip_local,
            ReuseAddr => 1,
	    Proto => 'udp'
	) ; 

	if (! $psock) {
	  	print STDOUT "Could not create listening socket ($!)\n";
	}

	print DEBUGTHREE "MLease is configured to unicast traffic ";
	print DEBUGTWO "using $ip_local\:$local \n";
	
}


## Subroutine to configure port to listen for broadcasted DHCP traffic.
#######################################################################
sub setupLocalSocket {
    my $ip_local = shift;
	
	$psock = IO::Socket::INET->new(
		LocalPort => 68, 
		LocalAddr => $ip_local,
		ReuseAddr => 1,
		Proto => 'udp',
		Broadcast => 1
        );
	my $psock_err = $!;

	# Create second listening socket for broadcst replies
	$bsock = IO::Socket::INET->new(
		LocalPort => 68, 
		LocalAddr => inet_ntoa(INADDR_BROADCAST),
		ReuseAddr => 1,
		Proto => 'udp',
		Broadcast => 1
        );
	my $bsock_err = $!;

	if (! $psock){
		print STDOUT "Could not create sending socket ($psock_err)\n ";
	}
	if (! $bsock){
		print STDOUT "Could not create broadcast listening socket ($bsock_err)\n ";
	}

	print DEBUGTHREE "MLease is configured to broadcast traffic ";
	print DEBUGTWO "using port $local \n";
			
}


## Subroutine to set the logging levels.
########################################
sub setUpLoggingLevels {
  
#tie (*BOTH,'Tie::FileHandle::MultiPlex', *LOG, *STDOUT);
## DEFINE the filehandle BOTH to print to screen and log.
my $fh1=*NULL;
my $fh2=*NULL;
my $fh3=*NULL;
my $prog=*NULL;

#  	if($screenLogging==1){$progressBar=1;}
  	$progressBar=0;
#  	if (!$logfile) {
  	if (1) {
		# Debug logging levels to the screen are as follows:
		#       Debug 3 is "play by play", summaries and  packet diagram
		#       Debug 2 is "play by play" and summary
		#       Debug 1 is "progress bar" and summary
		#       Debug 0 is just the summaries.
		if ($screenLogging == 3){
      			$fh3=*STDOUT;
			open (DEBUGTHREE,">&STDOUT");
      			$fh2=*STDOUT;
			open (DEBUGTWO,">&STDOUT");
      			$fh1=*STDOUT;
			open (DEBUGONE,">&STDOUT");
    		} elsif ($screenLogging == 2){
      			$fh2=*STDOUT;
			open (DEBUGTWO,">&STDOUT");
      			$fh1=*STDOUT;
			open (DEBUGONE,">&STDOUT");
    		} else {
			$fh1=*STDOUT;
			open (DEBUGONE,">&STDOUT");
      			if ($progressBar==1) {
       				$prog=*STDOUT;
				open (PROGRESS,">&STDOUT");
      			}
		}
  	} else {
		# This is the combination of screen and file logging matrix
    		if ($screenLogging == 3){
      			$fh3=*STDOUT;
      			if ($fileLogging ==3) { $fh3=*BOTH; } 
      			$fh2=*STDOUT;
      			if ($fileLogging >=2) { $fh2=*BOTH; } 
      			$fh1=*STDOUT;
      			if ($fileLogging >=1) { $fh1=*BOTH; } 
    		} elsif ($screenLogging >= 2){
      			if ($fileLogging ==3) { $fh3=*LOG; }
      			$fh2=*STDOUT;
      			if ($fileLogging >=2) { $fh2=*BOTH; }
      			$fh1=*STDOUT;
      			if ($fileLogging >=1) { $fh1=*BOTH; }
    		} elsif ($screenLogging >= 0){
      			if ($fileLogging ==3) { $fh3=*LOG; }
      			if ($fileLogging >=2) { $fh2=*LOG; }
      			$fh1=*STDOUT;
      			if ($fileLogging >=1) { $fh1=*BOTH; }
      			if ($progressBar==1) {
       				$prog=*STDOUT;
      			}
    		} else {
			# Debug logging levels to a file are as follows:
			#       Debug 3 is "play by play", summaries and  packet diagram
			#       Debug 2 is "play by play" and summary
			#       Debug 1 is just the summaries.
      			if ($fileLogging ==3) { $fh3=*LOG; }
      			if ($fileLogging >=2) { $fh2=*LOG; }
      			if ($fileLogging >=1) { $fh1=*LOG; }
    		}  
  	}
#  	tie (*PROGRESS,'Tie::FileHandle::MultiPlex', $prog);
#  	tie (*DEBUGONE,'Tie::FileHandle::MultiPlex', $fh1); 
#  	tie (*DEBUGTWO,'Tie::FileHandle::MultiPlex', $fh2); 
#  	tie (*DEBUGTHREE,'Tie::FileHandle::MultiPlex', $fh3); 
}


## Subroutine for Packet Display Formating.
###########################################
sub packetPrinter {
my $packet = $_[0];
my $decodedPacket=unpack("H*",$packet);
my $ascii="";

print DEBUGTHREE "\n\n          | 00 01 02 03 04 05 06 07 08 09 0a 0b 0c 0d 0e 0f\n";   
print DEBUGTHREE "     -----+------------------------------------------------\n";
print DEBUGTHREE "     0000 | ";    
my $g=0;
my $h=0;
    while ($decodedPacket){  
      $decodedPacket=~/(..)([0-9a-fA-F]*)/;
      print DEBUGTHREE $1." ";
      $decodedPacket=$2;
      if ($1=~/([2-7].)/){
         $ascii.=chr(hex($1));
      }else{
	 $ascii.=".";
      }
      $g++;
      if($g>=16){
        $g=0;
        $h+=16;
        print DEBUGTHREE " $ascii\n     ".sprintf("%004x",$h)." | ";
	$ascii="";
      }
    }
    for ($g; $g<=15; $g++) { print DEBUGTHREE "   "; }
    print DEBUGTHREE " $ascii\n\n";
} 

## Subroutine to build BootP packet headers.              
############################################
sub bootp_header {
  ## params: xid,ciaddr,yiadddr,siaddr,giaddr,chaddr
  my $packet="";
  my $msg_type=pack("H2","01");           # Boot Request = 1
  my $hw_type=pack("H2","01");            # Ethernet = 1
     if ($hw_addr_length==0) {$hw_type=pack("H2","00");}
  my $hw_len=pack("h2", $hw_addr_length); # Default = 6, max = 16
                                          #  If hw_addr_length = 0
					                      #  hw_type also = 0
  my $hops=pack("H2", "0");               # Number of router hops.
  my $transid=pack("H8", $_[0] );         # Transaction ID - 
                                          #   1st parameter.
  my $seconds=pack("H4","0");             # Packet Timer.
  my $bcast_bit=pack("H4", "8000");       # Broacdast Flag, 0x8000
                                          #   set - 0x0000 unset.
  my $ciaddr=$_[1];                       # CIADDR - IP Address
                                          #   Client is using.
  my $yiaddr=$_[2];                       # YIADDR - Address offered
                                          #   from DHCP Server.
  my $siaddr=$_[3];                       # SIADDR - Next Server in
                                          #   bootstrap.
  my $giaddr=$_[4];                       # GIADDR - Router passing
                                          #   along DHCP Packet.
  my $chaddr=$_[5];                       # Client Hardware Address.
     if ($hw_addr_length==0) {$chaddr="000000000000";}
  my $sname=pack("H128", $sName);         # Boot Server Name Field,
                                          #   Option 66
  my $bootfile=pack("H256", $bootFile);   # Boot File Name, Option 67
  my $cookie=pack("H8", $magicCookie);    # Magic Cookie - Required.
  my $packet="";
    if (length($hw_addr_length) > 1) {$hw_len=pack("H2", "10"); }
    if ($ciaddr ne INADDR_ANY){$ciaddr = &inet_2_hex($ciaddr);}
    if ($yiaddr ne INADDR_ANY){$yiaddr = &inet_2_hex($yiaddr);}
    if ($siaddr ne INADDR_ANY){$siaddr = &inet_2_hex($siaddr);}
    if ($giaddr ne INADDR_ANY){$giaddr = &inet_2_hex($giaddr);}
    $chaddr=pack("H12 H20", $chaddr, "0");
    $packet  = $msg_type.$hw_type.$hw_len;
    $packet .= $hops.$transid.$seconds.$bcast_bit;
    $packet .= $ciaddr.$yiaddr.$siaddr.$giaddr;
    $packet .= $chaddr.$sname.$bootfile.$cookie;
    return $packet;
}


## Subroutine to add convert a DHCP/BootP option to a hex string in
##   the correct format.
##   Supports options 12,15,40,43,50,51,53,54,55,60,61,77,81,82,118,250
#######################################################################
sub option_packer {
  my $opt = $_[0];  # Option Number in Decimal
  my $temp = $_[1]; # Value of the Option.
  my $templen = length($temp);
  my $temphex = "";
  my @temparray = "";
  my $i="";
    $temphex .= &dec2hex($opt);
    if ($opt eq "81") {
      if ($opt81flag) {
	$temphex .= &dec2hex($templen/2+3).&dec2hex($opt81flag)."00"."00";
	$temphex .= $temp;
      } else {
	$temphex .= &dec2hex($templen+3)."000000";
	$temphex .= &str2hex($temp);
      }
    } elsif ($opt eq "55") {
      $templen = split(/,/, $temp);
      @temparray = split(/,/, $temp);
      $temphex .= &dec2hex($templen);
      for ($i=0; $i < $templen; $i++){
	$temphex .= &dec2hex($temparray[$i]);
      }
    } elsif (($opt eq "12")||($opt eq "15")||($opt eq "40")||
             ($opt eq "60")) {
      $temphex .= &dec2hex($templen);
      $temphex .= &str2hex($temp);
    } elsif ($opt eq "61") {
      my $hwtype = "01";
      if ($hw_addr_length > 16) {$hw_addr_length=16;}
      if ($phone) {$hw_addr_length=length($phone); $hwtype = "00";}
      $temphex .= &dec2hex($hw_addr_length + 1).&dec2hex($hwtype);
      if ($phone) {$hw_addr_length=06;}
      while (length($temp) < ($hw_addr_length * 2)) { $temp .= "ab";}
      $temphex .= $temp;      
    } elsif (($opt eq "50")||($opt eq "54")||($opt eq "118")) {
      $temphex .= sprintf("%02x", "4");
      while ($temp =~ /\./g) {
	      $temphex .= &dec2hex($`);
	      $temp = $';
      }
      $temphex .= &dec2hex($temp);
    } elsif (($opt eq "43")||($opt eq "51")||($opt eq "53")||
             ($opt eq "77")||($opt eq "82")||($opt eq "250")) {
      $temphex .= &dec2hex($templen/2);
      $temphex .= $temp;
    } else {
      print STDOUT "No rule for this option.\n";
    }
    $templen=0;
    return $temphex;
}


## Subroutine to convert IP address to a HEX stream.
####################################################
sub inet_2_hex {
  my $ip="";
  my $temp = shift;
  my @a;
    @a=split(/\./,$temp);
    foreach my $a (@a) {
       $ip .= &dec2hex($a);
    }
    $ip = pack("H8",$ip);
    return $ip;
}


## Subroutine to Convert Decimal to HEX.
########################################
sub dec2hex {
  my $decnum=shift;
  my $hexnum;
  my $tempval;
    while ($decnum != 0) {
	    $tempval = $decnum % 16;
	    if ($tempval > 9) {
		    $tempval = chr($tempval + 55);
	    }
	    $hexnum = $tempval . $hexnum;
	    $decnum = int($decnum / 16);
	    if ($decnum < 16 ) {
		    if ($decnum > 9) {
			    $decnum = chr($decnum + 55);
		    }
		    $hexnum = "${decnum}${hexnum}";
		    $decnum = 0;
	    }
    }
    if (!$hexnum) { $hexnum = "00"; }
    return $hexnum;
}


## Subroutine to Convert String To HEX.
#######################################
sub str2hex {
	my $string=shift;
	return unpack("H*","$string");
}


## Subroutine to DNS encode a FQDN
##################################
sub dnsEncode {
	my $fqdn=$_[0];
	my @a=split('\.',$fqdn);
	my $label;
	my $dnsencode = "";
	foreach $label (@a) {
		my $len=length($label);
		my $hlen=&dec2hex($len);
		my $hex=&str2hex($label);
		$dnsencode.="${hlen}${hex}";
	}
	$dnsencode.="00";
	return $dnsencode;
}
	
	
## Subroutine to increment MAC Addresses
########################################
sub inc_mac {
  my $ch_suffix=$_[0];
    $ch_suffix = hex($ch_suffix);
    $ch_suffix++;
    if (($ch_suffix > 16777214)&&($ch_prefix eq "ffffff")){
      $ch_suffix = 0;
    }elsif($ch_suffix > 16777215){
      $ch_suffix = 0;
      if ($ch_prefix eq "000000"){ 
        $ch_suffix = 1;
      }
    }
    $ch_suffix=sprintf("%06x",$ch_suffix);
    return $ch_suffix;
}


## Subroutine to create a complete DHCP option block.
#####################################################
sub option_stuffer{
  my $o53=$_[0];
  my $o61=$_[1];
  my $ops=$_[2];
  my $stuffed=&option_packer(53,$o53);
    if ($phone) {
	    # if (length($phone)==10){
        my $hexphone="";
        my @phone = split (//,$phone);
        foreach my $n (@phone) {
	   $hexphone .= sprintf("%02x", ord($n)); 
	   # $hexphone .= "3${n}";
	   # }
        $o61=$hexphone;
      }
    }
    $stuffed .= &option_packer(61, $o61); 
    chomp($ops);
    if ((length($ops) % 2) == 0){
      $stuffed .= $ops; 
    } else {   
      print STDOUT "Warning: problems with your options:\n\t$ops\n";          
    }
    $stuffed = pack("H*", $stuffed);
    $stuffed .= pack("H2", $optionTerminator);
    return $stuffed;
}


## Subroutine to quickly decode DHCP option blocks.
###################################################
sub decimalOptionDecodeAndHash{
my $chaddr=$_[0];
my $opts=$_[1];
my $sname=$_[2];
my $bootfile=$_[3];
my $overload=0;
my @options=();
  while ($opts){
    my $decimalOption=hex(substr($opts, 0, 2));
    if ($decimalOption < 255) {
      if ($decimalOption == 52){
        $opt52=substr($opts, 5, 1);
        $overload=substr($opts, 6);
        next;
      }
      push(@options, $decimalOption);      
      my $pointer=2*hex(substr($opts, 2, 2));
      $opts=substr($opts, $pointer+4);
    } else { 
      if ($overload==1){
        $opts=$bootfile;
      }elsif ($overload==2){
        $opts=$sname;
      }elsif ($overload==3){
        $opts=$bootfile;
        $overload=2;
      }
      last;
    }
  }
  ## add mac-options hash table
  $serverOptions{$chaddr}="@options";
}


## Subroutine to decode a DHCP option block from a server.
##########################################################
sub decodeOptions{
  my $opts=$_[0];
  my $sname=$_[1];
  my $bootfile=$_[2];
  my $overload=0;
  chomp($opts);
  print DEBUGONE "  -----------------------\n";
  print DEBUGONE "  -- Last packet options:\n";
  print DEBUGONE "  -----------------------\n";
  while($opts){
    if ($opts =~ /^3501/){
      $opts=$';
      if ($opts =~ /^02/){
        print DEBUGONE "  Option  53 : DHCP OFFER\n";
      } elsif ($opts =~ /^05/){
        print DEBUGONE "  Option  53 : DHCP ACK\n";
      } elsif ($opts =~ /^06/){
        print DEBUGONE "  Option  53 : DHCP NACK\n";
      } elsif ($opts =~ /^0b/){
	print DEBUGONE "  Option  53 : DHCP LEASE UNASSIGNED\n";
      } elsif ($opts =~ /^0c/){
	print DEBUGONE "  Option  53 : DHCP LEASE UNKNOWN\n";
      } elsif ($opts =~ /^0d/){
	print DEBUGONE "  Option  53 : DHCP LEASE ACTIVE\n";
      }
      $opts=$';      
    } elsif ($opts =~ /^3401/){
      $opts=$';
      $overload=substr($opts, 1, 2);
      $opts=substr($opts, 2);
    } elsif ($opts =~ /^ff/) {
      $opts="";
      if ($overload==1){
        $opts=$bootfile;
      }elsif ($overload==2){
        $opts=$sname;
      }elsif ($overload==3){
        $opts=$bootfile;
        $overload=2;
      }
#      print DEBUGONE "  Option Terminator: ff\n\n";
      print DEBUGONE "  Option End : ff\n\n";
    } elsif ($opts =~ /^00/) {
#      print DEBUGONE "  Option Padding: $opts\n";
      print DEBUGONE "  Option Pad : $opts\n";
      $opts="";
    } else {
      my $pointer=2*hex(substr($opts, 2, 2));
      my $decimalOption=hex(substr($opts, 0, 2));
      printf DEBUGONE "  Option %3u : ", $decimalOption;
      if (($decimalOption== 1)||($decimalOption== 3)||($decimalOption== 4)||($decimalOption== 5)||
          ($decimalOption== 6)||($decimalOption== 7)||($decimalOption== 8)||($decimalOption== 9)||
	  ($decimalOption==10)||($decimalOption==11)||($decimalOption==16)||($decimalOption==28)||
	  ($decimalOption==32)||($decimalOption==33)||($decimalOption==41)||($decimalOption==42)||
	  ($decimalOption==44)||($decimalOption==45)||($decimalOption==48)||($decimalOption==49)||
	  ($decimalOption==54)||($decimalOption==65)||($decimalOption==68)||($decimalOption==69)||
	  ($decimalOption==70)||($decimalOption==71)||($decimalOption==72)||($decimalOption==73)||
	  ($decimalOption==74)||($decimalOption==75)||($decimalOption==76)||($decimalOption==85)||
          ($decimalOption==92)){
        my $point=4;
        while ($point<=$pointer){
          for (my $i=1; $i<=3; $i++){ 
            print DEBUGONE hex(substr($opts, $point, 2)).".";
            $point+=2;
          }
        print DEBUGONE hex(substr($opts, $point, 2))." ";
        $point+=2;         
        }
        print DEBUGONE "\n";
      } elsif ($decimalOption==51){
#        print DEBUGONE "(Lease time) ".hex(substr($opts, 4, $pointer))." seconds\n";
        print DEBUGONE hex(substr($opts, 4, $pointer))."\n";
      } elsif ($decimalOption==91){
#	print DEBUGONE "(Last Transaction) ".hex(substr($opts, 4, $pointer))." seconds\n";
	print DEBUGONE hex(substr($opts, 4, $pointer))."\n";
      } elsif (($decimalOption==12)||($decimalOption==14)||($decimalOption==15)||($decimalOption==17)||
               ($decimalOption==18)||($decimalOption==40)||($decimalOption==60)||
	       ($decimalOption==64)||($decimalOption==77)){
        my $sample=substr($opts, 4, $pointer);
        while ($sample){
          print DEBUGONE chr(hex(substr($sample, 0, 2)));
          $sample=substr($sample, 2, );
        } 
        print DEBUGONE "\n";       
      } elsif ($decimalOption==81){
        my $sample=substr($opts, 10, $pointer-6);
        print DEBUGONE "[".substr($opts, 4, 6)."] ";
        while ($sample){
          print DEBUGONE chr(hex(substr($sample, 0, 2)));
          $sample=substr($sample, 2, );
        } 
        print DEBUGONE "\n";       
      } else {
        print DEBUGONE substr($opts, 4, $pointer)."\n";
      }
      $opts=substr($opts, $pointer+4,);
    }
  } 
}

    

## Subroutine to listen for DHCP server responses.
##################################################
sub listen_for_packet {
  my $datagram = "";
  my @packet="";
  my $type="";
  my $serv="";
  my $sel = IO::Select -> new($psock);
  if ($local == 68)
  {
    $sel->add($bsock);
  }
  my @ready = $sel -> can_read($timeOutWaiting);
  if (@ready){
    $ready[0]->recv($datagram,3000) || next; 
    my $bootpType=unpack("H2",substr($datagram,0,1));
    my $xid=unpack("H8",substr($datagram,4,4));
    my $ciaddr=inet_ntoa(substr($datagram,12,4));
    my $yiaddr=inet_ntoa(substr($datagram,16,4));
    my $siaddr=inet_ntoa(substr($datagram,20,4)); 
    my $giaddr=inet_ntoa(substr($datagram,24,4));
    my $chaddr=unpack("H*",substr($datagram,28,6));
    my $sname=substr($datagram,44,64);
    my $bootfile=substr($datagram, 108, 128);
    my $options=unpack("H*",substr($datagram,240));
    my $source_ip = inet_ntoa($psock->peeraddr);
    if ($bootpType eq "02") {
      if ($options =~ "^3501") {
        if ($' =~ "^02") {
          $options =~ "3604";
          $serv = inet_ntoa(pack("H8",substr($',0,8)));

          # Skip reply from unexpected server IP
          if ($expected_server && ($serv ne $expected_server))
          {
              print DEBUGTWO "Skipping unexpected response from '$source_ip', '$serv' not '$expected_server'\n";
              next;
          }
          print DEBUGTWO "Received DHCP OFFER from $serv (source: $source_ip) for $chaddr to use $yiaddr";
          $type="DHCP OFFER";
          print PROGRESS "O";
          if ((@with)||(@without)){
            decimalOptionDecodeAndHash($chaddr, $options, $sname, $bootfile);
          }
        } elsif ($' =~ "^05") {
          $options =~ "3604";
          $serv = inet_ntoa(pack("H8",substr($',0,8)));

          # Skip reply from unexpected server IP
          if ($expected_server && ($serv ne $expected_server))
          {
              print DEBUGTWO "Skipping unexpected response from '$source_ip', '$serv' not '$expected_server'\n";
              next;
          }
          print DEBUGTWO "Received DHCP ACK from $serv (source: $source_ip) for $chaddr to use $yiaddr";
          $type="DHCP ACK";
          print PROGRESS "A";
        } elsif ($' =~ "^06") {
          $options =~ "3604";
          $serv = inet_ntoa(pack("H8",substr($',0,8)));

          # Skip reply from unexpected server IP
          if ($expected_server && ($serv ne $expected_server))
          {
              print DEBUGTWO "Skipping unexpected response from '$source_ip', '$serv' not '$expected_server'\n";
              next;
          }
          print DEBUGTWO "Received NACK from $serv (source: $source_ip) for $chaddr";
          $type="DHCP NACK";
          print PROGRESS "N";
        } elsif ($' =~ "^0b") {

          # Skip reply from unexpected server IP
          if ($expected_server && ($source_ip ne $expected_server))
          {
              print DEBUGTWO "Skipping unexpected response from '$source_ip', '$serv' not '$expected_server'\n";
              next;
          }
	  print DEBUGTWO "Received DHCP LEASE UNASSIGNED (sourceL $source_ip) for $ciaddr\n";
	  $type="DHCP LEASE UNASSIGNED";
	  print PROGRESS "U";
        } elsif ($' =~ "^0c") {

          # Skip reply from unexpected server IP
          if ($expected_server && ($source_ip ne $expected_server))
          {
              print DEBUGTWO "Skipping unexpected response from '$source_ip', '$serv' not '$expected_server'\n";
              next;
          }
	  print DEBUGTWO "Received DHCP LEASE UNKNOWN (source: $source_ip)\n";
	  $type="DHCP LEASE UNKNOWN";
	  print PROGRESS "u";
	} elsif ($' =~ "^0d") {

          # Skip reply from unexpected server IP
          if ($expected_server && ($source_ip ne $expected_server))
          {
              print DEBUGTWO "Skipping unexpected response from '$source_ip', '$serv' not '$expected_server'\n";
              next;
          }
	  print DEBUGTWO "Received DHCP LEASE ACTIVE (source: $source_ip) for $chaddr to use $ciaddr\n";
	  $type="DHCP LEASE ACTIVE";
	  print PROGRESS "A";
        }
      } else {

        # Skip reply from unexpected server IP
        if ($expected_server && ($sname !~ /^${expected_server}[\0]*$/))
        {
            print DEBUGTWO "Skipping unexpected response from '$source_ip', '$sname' not '$expected_server'\n";
            next;
        }
        print DEBUGTWO "Received BootP REPLY for $chaddr to use $yiaddr\n\tfrom $sname (source: $source_ip)\n";
        $type="BootP REPLY";
        $serv="$expected_server";
        print PROGRESS "b";
      }
      @packet=($xid, $ciaddr, $yiaddr, $siaddr, $giaddr, $chaddr, $type, $serv, $options);
      @detailpacket=($xid, $ciaddr, $yiaddr, $siaddr, $giaddr, $chaddr, $sname, $bootfile, $options);
    } elsif ($bootpType eq "01") {
      print DEBUGTWO "Response was not from a server (Msg 1,3,4,7,8,10) (source: $source_ip)"; 
      $type="BootP REQUEST";
    }
    if (($fileLogging==3)||($screenLogging==3)){
	    packetPrinter($datagram);
    }
  } else {
    $packet[6]="timeout";
    print DEBUGTWO "TIMED OUT waiting for response. \n";
    print PROGRESS "t";
  }
  return @packet;
}


## Subroutine to send packets
#############################
sub sendMsg {
	my $packet=$_[0];
	my $type=$_[1];
	my $ch=$_[2];

	if ($server ne "255.255.255.255"){
		print DEBUGTWO "Sending $type from $specificInterface to"; 
		foreach my $sendTo (@serverArray) {
			print DEBUGTWO " $sendTo";
			my $sin=pack_sockaddr_in('67',inet_aton($sendTo));
			$psock->send($packet,0,$sin);
		}
		if (($ch ne "000000000000")&&($dhcpLeaseQueryType ne "ip")){
			print DEBUGTWO " for $ch";
		}
		print DEBUGTWO " (server=$server)\n";
	} else {
		print DEBUGTWO "Broadcasting $type from $specificInterface\n";
		my $sin=pack_sockaddr_in('67',INADDR_BROADCAST);
		$psock->send($packet,0,$sin);
	}
}



## Subroutine to send and collect packets.
###################################################
sub sendReceive {
  ## Sending packet specified in the toDoList.
  my $i=0;
  my @temparray=();
#  while(@toDoList){
    my $packet="";
    my $xi=$toDoList[0];
    my $ci=$toDoList[1];
    my $yi=$toDoList[2];
    my $si=$toDoList[3];
    my $gi=$toDoList[4];
    my $ch=$toDoList[5];
    my $ty=$toDoList[6];
    my $type="";
    my $op=$toDoList[8];
    if ($ty eq "DHCP DISCOVER"){
      $type="01";
      $i++;
      if ($xi =~/^ffff/) {
        ## sendOnly hot xid
        $i--;
      }
      $discount++;
      print PROGRESS "D";
      push (@temparray, splice(@toDoList, 0, 9));
    } elsif ($ty eq "DHCP REQUEST"){
      $type="03";
      $i++;
      if ($xi =~/^ffff/) {
        ## sendOnly hot xid
        $i--;
      }
      $reqcount++;
      print PROGRESS "R";
      push (@temparray, splice(@toDoList, 0, 9));
    } elsif ($ty eq "DHCP DECLINE"){
      $op="";
      $type="04";
      $deccount++;
      print PROGRESS "d";
      splice(@toDoList, 0, 9);
    } elsif ($ty eq "DHCP RELEASE"){
      $op="";
      $type="07";
      $relcount++;
      print PROGRESS "r";
      splice(@toDoList, 0, 9);
    } elsif ($ty eq "DHCP INFORM"){
      $type="08";
      $infcount++;
      $ch="000000000000";
      print PROGRESS "i";
      # push (@temparray, splice(@toDoList, 0, 9));
      splice(@toDoList, 0, 9);
    } elsif ($ty eq "DHCP LEASE QUERY"){
      $type="0a";
      push (@temparray, splice(@toDoList, 0, 9));
    } elsif ($ty eq "Bad Packet"){
      print PROGRESS "-";
      $type="00";
      splice(@toDoList, 0, 9);
      my $temppacket=<<stupid;
      01010600ffffffff006c742f000000000000000000000000000000006969000055555555555500555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555005555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555
stupid
      while ($temppacket) {
        my $chunk = substr($temppacket,0,2);
        $packet.=pack("H2",$chunk);
        $temppacket = substr($temppacket,2);
      }
      $badPacketCounter++;
    } elsif ($ty eq "NT RAS Packet"){
      print PROGRESS "~";
      $type="00";
      splice(@toDoList, 0, 9);
      my $temppacket="01011000".$xi."0000000000000000000000000000000000000000".$ch."0708090a0b0c0d0e0f10";
      while ($temppacket) {
        my $chunk = substr($temppacket,0,2);
        $packet.=pack("H2",$chunk);
        $temppacket = substr($temppacket,2);
      }
      $packet.=pack("H128",0);
      $packet.=pack("H256",0);
      $packet.=pack("H20","638253633501013d1101");
      $packet.=pack("H12",$ch);
      $packet.=pack("H20", "0708090a0b0c0d0e0f10");
      $packet.=pack("H50", "37070103060f2c2e2f0c0d5241532d53696d756c61746f72ff");
      $discount++;
    } elsif ($ty eq "2K RAS Packet"){
      $toDoList[6]="DHCP DISCOVER";
      $op="";
      $type="09";
      $discount++;
      $i++;
      print PROGRESS "~";
      #splice(@toDoList, 0, 9);
      push (@temparray, splice(@toDoList, 0, 9));
   } else {
      ## this is a BootP Request Packet
      $i++;
      print PROGRESS "B";
      $bootpRequest++;
      $packet=&bootp_header($xi, $ci, $yi, $si, $gi, $ch);
      $packet .= pack("H2", "ff");
      $packet .= pack("H121", "00");
      push (@temparray, splice(@toDoList, 0, 9));
    }
    if ($type =~ /0[1,3,4,7]/ ) {
      $packet=&bootp_header($xi, $ci, $yi, $si, $gi, $ch);
      $packet .= &option_stuffer($type, $ch, $op)
    } elsif ($type eq "08") {
      $packet=&bootp_header($xi, $ci, $yi, $si, $gi, $ch);
      #Hand pack INFORM options
      $packet .= pack("H16", "3501082b025e00ff");
    } elsif ($type eq "09") {
      $packet=&bootp_header($xi, $ci, $yi, $si, $gi, $ch);
      #Hand pack 2K RAS options And put them in the hash
      $packet .= pack("H6","350101");
      $op = &option_packer(77, &str2hex("RRAS.Microsoft"));
      $op.= "fb01013d110152415320".$ch."123456789abc";
      $op.= &option_packer(12, "Win2k-RAS");
      $op.= &option_packer(60, "MSFT 5.0");
      $op.= &option_packer(55, "1,15,3,6,44,46,47,31,33,43");
      $clientOptions{$ch}=$op;
      $op.= "ff";
      $packet .= pack("H146", $op);
    } elsif ($type eq "0a") {
      # Hand pack DHCP LEASE QUERY options
      $i++;
      # Query By IP Address
      if ($dhcpLeaseQueryType eq "ip") {
	$hw_addr_length=0;
	$packet=&bootp_header($xi, $ci, $yi, $si, $gi, "000000000000");
        $packet .= pack("H6","35010a");
      # Query By MAC Address
      } elsif ($dhcpLeaseQueryType eq "mac") {
	$packet=&bootp_header($xi, $ci, $yi, $si, $gi, $ch);
	$packet .= pack("H6","35010a");
	if ($ch eq "000000000000") {  
	  # We should only get here if we are using an input file.
	  # The $hw_addr_length statement will set up the top of the
	  #  packet for queries by id and ip.
	  $hw_addr_length=0;
	  $packet=&bootp_header($xi, $ci, $yi, $si, $gi, "000000000000");
	  $packet .= pack("H6","35010a");
	  # print "op-->$op\n";
	  # $packet .= pack("H*","$op");
	  $hw_addr_length=6;
	  if ($ci eq "0.0.0.0" ) {
	    # If we get here than this is a query by id and it needs
	    #  to have option 61 in the packet.
	    # $packet .= pack("H*",$op);
          }
        }
	$packet .= pack("H*","$op");
      # Query By Client ID
      } elsif ($dhcpLeaseQueryType eq "id") {
	$hw_addr_length=0;
	$packet=&bootp_header($xi, $ci, $yi, $si, $gi, "000000000000");
	$packet .= pack("H6","35010a");
	$packet .= pack("H18","3d0701$ch");
      }
      if ($opt55) {
	$packet .= pack("H*", &option_packer(55, $opt55));
      }
      $packet .= pack("H2","ff");
      print PROGRESS "Q";
      $lqcount++;
    }
    sendMsg($packet, $ty, $ch);
    if (($fileLogging==3)||($screenLogging==3)){
      packetPrinter($packet);
    }
#  }
  if ($sendOnly) {$i=0;}  

  ## Receiving Packets
  my $j=0;
  # if ($dualserver){$i*=2;}
  while ($i > 0 ) {
    @dhcppacket=&listen_for_packet();
    ###### Deal with timeouts ######
    if ($dhcppacket[6] eq "timeout"){
      $i--; $j++;
      if ($j==$timeOutGiveUp) { last; }
    ###### Deal with offers ######
    } elsif ($dhcppacket[6] eq "DHCP OFFER"){
      $j=0;
      if (($dhcppacket[7] eq $server)||
          ($dhcppacket[7] eq $foserver)||
          ($dhcppacket[7] eq $dualserver)||
          ($local==68)) {
        my $l=5;
        my $n=scalar(@temparray);
        while ($l <= $n){
          if (($dhcppacket[5] eq $temparray[$l])&&($temparray[$l+1] eq "DHCP DISCOVER")){
            splice(@temparray,($l-5), 9);
            last;
          } else {
            $l+=9;
          }
        } 
        if ($n>$l){
          if ($decodeOptionsServerPacket && $screenLogging >= 2){
            print DEBUGTWO "\n";
            print DEBUGTWO "\tciAddr: $dhcppacket[1]\n";
	    print DEBUGTWO "\tyiAddr: $dhcppacket[2]\n";
	    print DEBUGTWO "\tsiAddr: $dhcppacket[3]\n";
	    print DEBUGTWO "\tgiAddr: $dhcppacket[4]\n";
	    print DEBUGTWO "\tchAddr: $dhcppacket[5]\n";	  
            &decodeOptions($dhcppacket[8]);
          }
          #### Put formulate DHCP Request Subroutine here
          if (@with) { 
            my @so=split(/\s/, $serverOptions{$dhcppacket[5]});
            while(@with){
              my $wit=$with[$#with];
              foreach my $tmp(@so){
                if ($wit eq $tmp){
                  pop(@with);
                  last;
                }
              }
              if ($wit eq $with[$#with]) { 
                print DEBUGTWO "Client did not receive all the required options.\n\t\tNot sending DHCP REQUEST...\n";
                last;
              }  
            }
          }
          if (@without) {
            my @so=split(/\s/, $serverOptions{$dhcppacket[5]});
            my $match=0;
            while(@without){
              my $wo=$without[$#without];
              foreach my $tmp(@so){ 
                if ($wo eq $tmp){
                  $match=1;
                } else {
                }           
              }
              if ($match) { 
                last; 
              } else {
                pop(@without);
              }
            }
          }
          #### AKA Fussy Client.
          if ((!@with)&&(!@without)){
            my $reqAddr=$dhcppacket[2];
            $dhcppacket[2]=INADDR_ANY;
            $dhcppacket[6]="DHCP REQUEST";
            $dhcppacket[8]=&option_packer(50, $reqAddr).&option_packer(54,$dhcppacket[7]).$clientOptions{$dhcppacket[5]};
            push(@actionItems, @dhcppacket);
          } else {
            print PROGRESS chr(8)."x";
          }
          $i--;
          $offcount++;
        } else {
          print DEBUGTWO " for $dhcppacket[5]\n\tMAC address not found, or duplicate packet.\n\t\tDiscarding...\n";
          print PROGRESS chr(8)."I";
	  $ignoredPacketCounter++;
        } 
      } elsif ($dhcppacket[7] eq $splitserver){
        print DEBUGTWO "\n\tOFFER from the split scope server.\tIgnoring...\n";
        print PROGRESS chr(8)."I";
	$ignoredPacketCounter++;
      } else {
        print DEBUGTWO ", which is not under test.\n";
        print PROGRESS chr(8)."I";
	$ignoredPacketCounter++;
      }
    ###### Deal with ACKS ######
    } elsif ($dhcppacket[6] eq "DHCP ACK"){
      $j=0;
      if (($dhcppacket[7] eq $server)||
          ($dhcppacket[7] eq $foserver)||
          ($dhcppacket[7] eq $dualserver)||
          ($local==68)) {
        my $l=5;
        my $n=scalar(@temparray);
        while ($l <= $n){
	  #  It makes sense to accept both Offers and Requests as inputs for ACKS.
	  #    Since it is possible to code rapid commit in the input file as well
	  #    as on the command line.
          if (($dhcppacket[5] eq $temparray[$l])&&($temparray[$l+1] eq "DHCP REQUEST"||"DHCP OFFER")){
	    # The above line test for a MAC address that was sent and whether this
	    #   ACK is in response to a REQUEST or OFFER (Rapid Commit)
            splice(@temparray,($l-5), 9);
            last;
          } else {
            $l+=9;
          }
        } 
        if ($n>$l){
          my $oldAddr=$dhcppacket[2];
          if ($decodeOptionsServerPacket && $screenLogging >= 2){
            print DEBUGTWO "\n";
	    print DEBUGTWO "\tciAddr: $dhcppacket[1]\n";
	    print DEBUGTWO "\tyiAddr: $dhcppacket[2]\n";
	    print DEBUGTWO "\tsiAddr: $dhcppacket[3]\n";
	    print DEBUGTWO "\tgiAddr: $dhcppacket[4]\n";
	    print DEBUGTWO "\tchAddr: $dhcppacket[5]\n";
            &decodeOptions($dhcppacket[8]); 
          }
          ## Done Displaying ACK
          if ($dhcppacket[0] =~ /^\D\D\D\D/){
            ## Only xids that start with letter are post-processed. 
            my $test;
            if ($dhcppacket[0] =~ /^dddd/){
            ### Send DECLINE packet ###
              $test=$dhcppacket[0];
              $dhcppacket[0]=int(rand(99999999));
              $oldAddr=$dhcppacket[2];
              $dhcppacket[1]=$oldAddr;
              for (my $m=2; $m <= 4; $m++){
                $dhcppacket[$m]=INADDR_ANY;
              } 
              $dhcppacket[6]="DHCP DECLINE";
              $dhcppacket[8]="";
              push(@actionItems, @dhcppacket);
              ## ReDISCOVER after DECLINE
              if ($test !~ /^dddd..00/){
                my $count = substr($test,6,2);
                $count--;
                if ($count > 0){
		  $dhcppacket[0]="dddddd". sprintf("%2d",$count); # &dec2hex($count);
                } else { 
                  if ($inform) {
                    $dhcppacket[0]="cccc".sprintf("%2d", int(rand(99))).sprintf("%2d",$inform);
                  } elsif ($renew){
                    $dhcppacket[0]="bbbb".$renew.int(rand(9)).sprintf("%02d", $renewN);
                  } elsif ($release){
                    $dhcppacket[0]="eeee".$release.int(rand(9)).sprintf("%02d", $releaseN);
	          }
                }
                for (my $m=1; $m <= 3; $m++){
                  $dhcppacket[$m]=INADDR_ANY;
                } 
                $dhcppacket[4]=$giaddr;
                $dhcppacket[6]="DHCP DISCOVER";
                $dhcppacket[8]=&option_packer( 50, $oldAddr).$clientOptions{$dhcppacket[5]};
                unshift(@agenda, @dhcppacket);
              }
            ## end of DECLINE post processing
            } elsif ($dhcppacket[0] =~ /^cccc/){
            ### start of INFORM processing ###
              my $h=substr($dhcppacket[0],6,2);
	      my $tempciaddr=$dhcppacket[2];
              while ($h>0) {
                $dhcppacket[0]="ffffff".sprintf("%02d",$h);
		$dhcppacket[1]=$tempciaddr;
                $dhcppacket[2]=INADDR_ANY; 
                $dhcppacket[4]=$giaddr;
                $dhcppacket[6]="DHCP INFORM";
                $dhcppacket[8]=&option_packer( 43, "5e00");
                unshift(@agenda, @dhcppacket);
                $h--;
              }
              if ($renew){
                $dhcppacket[0]="bbbb".$renew.int(rand(9)).sprintf("%02d", $renewN);
                for (my $m=1; $m <= 3; $m++){
                  $dhcppacket[$m]=INADDR_ANY;
                } 
                $dhcppacket[4]=$giaddr;
                $dhcppacket[6]="DHCP DISCOVER";
                $dhcppacket[8]=&option_packer( 50, $oldAddr).$clientOptions{$dhcppacket[5]};
                unshift(@agenda, @dhcppacket);
              } elsif ($release){
                $dhcppacket[0]="eeee".$release.int(rand(9)).sprintf("%02d", $releaseN);
                for (my $m=1; $m <= 3; $m++){
                  $dhcppacket[$m]=INADDR_ANY;
                } 
                $dhcppacket[4]=$giaddr;
                $dhcppacket[6]="DHCP DISCOVER";
                $dhcppacket[8]=&option_packer( 50, $oldAddr).$clientOptions{$dhcppacket[5]};
                unshift(@agenda, @dhcppacket);
              }
            } elsif ($dhcppacket[0] =~ /^bbbb/){
            ### Start Renew post processing ###
              if ($dhcppacket[0] !~ /^bbbb..00/){ 
                my $count = substr($dhcppacket[0],6,2);               
                if ($count > 0){
                  $count--;
                  $dhcppacket[0]=substr($dhcppacket[0],0,6).sprintf("%02d", $count);
                  $dhcppacket[1]=$dhcppacket[2];
                  for (my $m=2; $m <= 3; $m++){
                     $dhcppacket[$m]=INADDR_ANY;
                  } 
		  	$dhcppacket[4]=$giaddr;
                  $dhcppacket[6]="DHCP REQUEST";
		  if ($opt82){
                    $dhcppacket[8]=substr($clientOptions{$dhcppacket[5]}, 0, -$o82len);
	          }else{
		    $dhcppacket[8]=$clientOptions{$dhcppacket[5]};
	          }
                }
                if ($dhcppacket[0] =~ /^....1/){
			if ($renewGiaddr){
				unshift(@agenda, @dhcppacket);
			} else {
				$dhcppacket[4]=INADDR_ANY;
				$dhcppacket[0]="ffffff00";
				for (my $p=1; $p<=$renewN; $p++){
					unshift(@agenda, @dhcppacket);
				} 
			}
                } else {
											       
			$dhcppacket[8].="030401020304";
			if ($renewGiaddr){
				push(@agenda, @dhcppacket);
			} else {
				$dhcppacket[4]=INADDR_ANY;
				$dhcppacket[0]="ffffff00";
				for (my $p=1; $p<=$renewN; $p++){
					push(@agenda, @dhcppacket);
				}
			}
                }                  
              } else {
                if ($release){
                  $dhcppacket[0]="eeee".$release.int(rand(9)).sprintf("%02d", $releaseN);
                  for (my $m=1; $m <= 3; $m++){
                    $dhcppacket[$m]=INADDR_ANY;
                  } 
                  $dhcppacket[4]=$giaddr;
                  $dhcppacket[6]="DHCP DISCOVER";
                  $dhcppacket[8]=&option_packer( 50, $oldAddr).$clientOptions{$dhcppacket[5]};
                  unshift(@agenda, @dhcppacket);
                }
              }
            ### End Renew post processing ###
            } elsif ($dhcppacket[0] =~ /^eeee/){
            ### Start RELEASE post processing ###
              my $test=$dhcppacket[0];
              $dhcppacket[0]="ffff".int(rand(9999));
              $dhcppacket[1]=$dhcppacket[2];
              for (my $m=2; $m <= 4; $m++){
                $dhcppacket[$m]=INADDR_ANY;
              } 
              $dhcppacket[6]="DHCP RELEASE";
              $dhcppacket[8]="";
              my $count=substr($test,6,2);
              $count--;
              if($count){
                $dhcppacket[0]=substr($test,0,6).sprintf("%02d", $count);
              } else {
                $dhcppacket[0]=int(rand(99999999));
              }
              ## Send RELEASE now and Do Nothing Else
              if ($test =~ /^eeee1/){
                push(@actionItems, @dhcppacket);
              ## Send RELEASE later and Do Nothing Else
              } elsif ($test =~ /^eeee2/){
                push (@agenda, @dhcppacket);
              ## Send RELEASE now and reDISCOVER
              } elsif ($test =~ /^eeee3/){
                push(@actionItems, @dhcppacket);
                for (my $m=1; $m <= 3; $m++){
                  $dhcppacket[$m]=INADDR_ANY;
                } 
                $dhcppacket[4]=$giaddr;
                $dhcppacket[6]="DHCP DISCOVER";
                $dhcppacket[8]=&option_packer( 50, $oldAddr).$clientOptions{$dhcppacket[5]};
                unshift(@agenda, @dhcppacket);
              } elsif ($test =~ /^eeee4/){
                unshift (@agenda, @dhcppacket);
                for (my $m=1; $m <= 3; $m++){
                  $dhcppacket[$m]=INADDR_ANY;
                } 
                $dhcppacket[4]=$giaddr;
                $dhcppacket[6]="DHCP DISCOVER";
                $dhcppacket[8]=&option_packer( 50, $oldAddr).$clientOptions{$dhcppacket[5]};
                push (@agenda, @dhcppacket);
              ## Send RELEASE later and reDISCOVER
              } elsif ($test =~ /^eeee5/){
                push (@agenda, @dhcppacket);
                for (my $m=1; $m <= 3; $m++){
                  $dhcppacket[$m]=INADDR_ANY;
                } 
                $dhcppacket[4]=$giaddr;
                $dhcppacket[6]="DHCP DISCOVER";
                $dhcppacket[8]=&option_packer( 50, $oldAddr).$clientOptions{$dhcppacket[5]};
                push (@agenda, @dhcppacket);
              } 
            }
          } 

          $ackcount++;
          $i--;
        } else {
          print DEBUGTWO " for $dhcppacket[5]\n\tMAC address not found, or duplicate packet.\n\t\tDiscarding...\n";
          print PROGRESS chr(8)."I";
	  $ignoredPacketCounter++;
        }
      } elsif ($dhcppacket[7] eq $splitserver){
        print DEBUGTWO "\n\t\tACK from the split scope server.\tIgnoring...\n";
        print PROGRESS chr(8)."I";
	$ignoredPacketCounter++;
      } else {
        print DEBUGTWO ", which is not under test.\n";
        print PROGRESS chr(8)."I";
	$ignoredPacketCounter++;
      } 
    ###### Deal with NACKS ######
    } elsif ($dhcppacket[6] eq "DHCP NACK"){
      $j=0;
      if (($dhcppacket[7] eq $server)||
          ($dhcppacket[7] eq $foserver)||
          ($dhcppacket[7] eq $dualserver)||
          ($local==68)) {
        my $l=5;
        my $n=scalar(@temparray);
        while ($l <= $n){
          if (($dhcppacket[5] eq $temparray[$l])&&($temparray[$l+1] eq "DHCP REQUEST")) {
            splice(@temparray,($l-5), 9);
            last;
          } else {
            $l+=9;
          }
        } 
        if ($n>$l){
          if ($decodeOptionsServerPacket && $screenLogging >= 2) {
            print DEBUGTWO "\n";
            print DEBUGTWO "\tciAddr: $dhcppacket[1]\n";
	    print DEBUGTWO "\tyiAddr: $dhcppacket[2]\n";
	    print DEBUGTWO "\tsiAddr: $dhcppacket[3]\n";
	    print DEBUGTWO "\tgiAddr: $dhcppacket[4]\n";
	    print DEBUGTWO "\tchAddr: $dhcppacket[5]\n";
            &decodeOptions($dhcppacket[8]);
          }
          $i--; 
          $nakcount++;
          if (($nack)||($dhcppacket[0] =~ /^aaaa3/)){
            for (my $m=1; $m <= 3; $m++){
              $dhcppacket[$m]=INADDR_ANY;
            } 
            $dhcppacket[4]=$giaddr;
            $dhcppacket[6]="DHCP DISCOVER";
            $dhcppacket[8]=$clientOptions{$dhcppacket[5]};
            unshift(@agenda, @dhcppacket);
          }
        } else {
          print DEBUGTWO " for $dhcppacket[5]\n\tMAC address not found, or duplicate packet.\n\t\tDiscarding...\n";
          print PROGRESS chr(8)."I";
	  $ignoredPacketCounter++;
        }
      } elsif ($dhcppacket[7] eq $splitserver){
        print DEBUGTWO "\n\tNACK from the split scope server.\tIgnoring...\n";
        print PROGRESS chr(8)."I";
	$ignoredPacketCounter++;
      } else {
        print DEBUGTWO ", which is not under test.\n";
        print PROGRESS chr(8)."I";
	$ignoredPacketCounter++;
      } 
    ###### Deal with BootP Replies ######
    } elsif ($dhcppacket[6] eq "BootP REPLY"){
      ## Deal With BootP Replys
      $j=0;
      if ($decodeOptionsServerPacket && $screenLogging >= 2){
        &decodeOptions($dhcppacket[8]); 
      } 
      $i--;
      $bootpReply++;
      my $l=5;
      my $n=scalar(@temparray);
      while ($l <= $n){
         if (($dhcppacket[5] eq $temparray[$l])&&($temparray[$l+1] eq "BootP REQUEST")) {            splice(@temparray,($l-5), 9);
	    last;
	 } else {
	    $l+=9;
	 }
      }
    ####### Deal with LEASE QUERY Stuff #######
    } elsif ($dhcppacket[6] eq "DHCP LEASE UNASSIGNED"){
       $j=0;
       if ($decodeOptionsServerPacket && $screenLogging >= 2){
	  print DEBUGTWO "\tciAddr: $dhcppacket[1]\n";
	  print DEBUGTWO "\tyiAddr: $dhcppacket[2]\n";
	  print DEBUGTWO "\tsiAddr: $dhcppacket[3]\n";
	  print DEBUGTWO "\tgiAddr: $dhcppacket[4]\n";
	  print DEBUGTWO "\tchAddr: $dhcppacket[5]\n";
	  &decodeOptions($dhcppacket[8]);
       }
       $i--;
       $lqunacount++;
       my $l=5;
       my $n=scalar(@temparray);
       while ($l <= $n){
	 if ($temparray[$l+1] eq "DHCP LEASE QUERY") {
	   splice(@temparray,($l-5), 9);
	   last;
	 } else {
	   $l+=9;
	 }
       }
    } elsif ($dhcppacket[6] eq "DHCP LEASE UNKNOWN"){
       $j=0;
       if ($decodeOptionsServerPacket && $screenLogging >= 2){
	 print DEBUGTWO "\tciAddr: $dhcppacket[1]\n";
	 print DEBUGTWO "\tyiAddr: $dhcppacket[2]\n";
	 print DEBUGTWO "\tsiAddr: $dhcppacket[3]\n";
	 print DEBUGTWO "\tgiAddr: $dhcppacket[4]\n";
	 print DEBUGTWO "\tchAddr: $dhcppacket[5]\n";
	 &decodeOptions($dhcppacket[8]);
       }
       $i--;
       $lqunkcount++;
       my $l=5;
       my $n=scalar(@temparray);
       while ($l <= $n){
	 if ($temparray[$l+1] eq "DHCP LEASE QUERY") {
           splice(@temparray,($l-5), 9);
	   last;
         } else {
           $l+=9;
         }
       }	 
    } elsif ($dhcppacket[6] eq "DHCP LEASE ACTIVE"){
       $j=0;
       if ($decodeOptionsServerPacket && $screenLogging >= 2){
          print DEBUGTWO "\tciAddr: $dhcppacket[1]\n";
          print DEBUGTWO "\tyiAddr: $dhcppacket[2]\n";
          print DEBUGTWO "\tsiAddr: $dhcppacket[3]\n";
          print DEBUGTWO "\tgiAddr: $dhcppacket[4]\n";
          print DEBUGTWO "\tchAddr: $dhcppacket[5]\n";
          &decodeOptions($dhcppacket[8]);
       }
       $i--;
       $lqactcount++;
       my $l=5;
       my $n=scalar(@temparray);
       while ($l <= $n){
	 if ($temparray[$l+1] eq "DHCP LEASE QUERY") {
	   splice(@temparray,($l-5), 9);
	   last;
	 } else {
	   $l+=9;
 	 }
       }										   
    ###### Everything else is unexpected ###### 
    } else {
      print DEBUGTWO "This response was unexpected!\n";
      print PROGRESS "x";
      $unexpectedPacketCounter++;
    }
  }
  if (@temparray){
    my $arraylen=$#temparray+1;
    my $to=$arraylen/9;
    $timeOutCounter+=$to;
    if ($reDiscoverTimeOuts) {
      if (($reDiscTimeOutsMaxTries + $numberOfMsgBunch) > $timeOutCounter){
        push(@agenda, @temparray);
      }
    }
  }
}


## Usage Subroutine
###################
sub usage {
  print <<END_USAGE;

Usage: $0 <flag> <value>

\tFlags\tValues
\t-a\tStarting Hardware Address in decimal. (default: 1)
\t-A\tStarting Hardware Address in hex. (default: 1)
\t-b\tSend a BootP REQUEST and wait for a BootP REPLY.
\t-bf\tFill in the bootfile section of packet.
\t-B\tSend a bad packet.
\t-c\tIP address to put in CIAddr field. (default: 0.0.0.0)
\t-cat\tSend Concatinated options.  Supported Option 81 and 250
\t-C\tCluster of discovers (default: 25)
\t-d\tTotal number of DISCOVER messages to send (default: 5)
\t-D\tHave client request a domain. [Option 15]
\t-en,-En\tFQDN value to pass to DHCP server. [Option 81]
\t\t\t-en Fixed; -En 5 digit numeric appendage.
\t\t\tWhere n is the numeric representation of the flag 
\t\t\tbyte.  A value of 0 is for ASCII encoding.  A 
\t\t\tvalue containing 4 will do DNS encoding.
\t-es\tOnly process responses from this server
\t-f\tName of the log file.
\t-file\tName of input file for canned test cases.
\t-F\tSend copy of the discover to the Failover DHCP server IP Addr
\t-g\tGIAddr - Router address (default: 0.0.0.0)
\t-h, -?\tShow Help - This screen.
\t-H\tComplete MAC Address (default: 0fffff000001)
\t\t\t Accepts key words zero and one.
\t-i\tSend INFORM after DORA. Enter number of INFORMs. (default: 0)
\t-if\tSelect a specific interface for binding. Values can represented
\t\t\t by interface name or IP Address.  (default: eth0)
\t-I1\tRelay Agent Option. [Option 82 Suboption 1] 
\t\t\tEnter Hex string for Circuit ID or 1 to have it generated.
\t-I2\tRelay Agent Option. [Option 82 Suboption 2]
\t\t\tEnter Hex string for Remote ID or 1 to have it generated.
\t-I4\tRelay Agent Option [Option 82 Suboption 4]
\t\t\t Valid value is 1.
\t-I5\tRelay Agent Option [Option 82 Suboption 5]
\t\t\tEnter IP address.
\t-I9\tRelay Agent Option [Option 82 Suboption 9]
\t\t\tEnter Hex string.
\t-Icisco\tTerminate packets containing Option 82 with pad.
\t-j\tDebug level for log Values: 1 - 3 (default: 2) 
\t-k\tReDISCOVER after NAK.  values 0 or 3 (default: 3)
\t-K\tOption 250 - enter hex string.
\t-l\tRELEASE address after DORA.  Values: (default: 1)
\t\t   1 RELEASE in this cluster
\t\t   2 RELEASE at the end of the trial
\t\t   3 reDISCOVER in next cluster after RELEASE (this cluster)
\t\t   4 reDISCOVER at end of trial after RELEASE (this cluster)
\t\t   5 reDISCOVER after RELEASE at the end of the trial
\t-lc\tRELEASE after DORA Counter (default: 1)
\t-L\tRequested lease time. (value in seconds or "i" for infinity) 
\t-LQ\tLEASE QUERY <type> <value>
\t\t\t<type> = ip, mac, id
\t\t\t<value> = IP address or MAC address where appropriate.
\t-m\tMAC Address prefix. (default: 0fffff)
\t-M\tDHCP message type (1 3 4 7 8 10) Disc, Req, Decl, Rel, Inf.
\t\t\tDHCP Lease Query
\t-n, -N\tHostname. [Option 12] (default: dhcp-client-xxxxx)
\t\t\t -n Fixed; -N 5 digit numeric appendage.
\t-NIS\tNIS Domain. [Option 40]  Enter String.
\t-NTRAS\tSend an NT RAS packet.  Do not wait for response.
\t-o\tOld IP Address. [Option 50].
\t-O\tOption Request List [Option 55] - comma seperated option list.
\t-p\tReceived packets from server will be decoded in debug 1 or higher.
\t-P\tClient Identifier [Option 61] - Enter 10 digit Phone Number or
\t\t\tan IP address in hex.
\t-q\tScreen logging level values 0 - 3 (default: 0) 
\t-r\tRenew address after DORA.  Values: (default: 1)
\t\t   1 RENEW in this cluster
\t\t   2 RENEW at the end of the trial
\t-rc\tNumber of DHCP renews after DORA. (default: 1)
\t-renew\t RENEW address. Enter CIADDR
\t-rg\tUse GIAddr for renews.  Values 0 or 1.  (default: 1)
\t-R\tDo not wait for server response.
\t-RC\tRapid Commit [Option 80]
\t-RAS2k\tSend an 2K RAS packet.  Do not wait for response.
\t-s\tDHCP server IP address. (default: 0.0.0.0)
\t-si\tServer Identifier for Renews (default: Nul)
\t-sn\tTFTP Server Name.
\t-ss\tDHCP split scope server IP address.
\t-S\tSubnet Selection Option. [Option 118]
\t-t\tTimes to repeat the DORA process.
\t-T\tNumber of trial summary printings to supress. (default:1) 
\t\t\tApplied only to Debug 0 and 1 output to the screen.
\t-u\tUser Class. [Option 77]
\t-U\tUser Class. [Option 77] as per RFC 3004.  Period delimited.
\t-v\tVersion information.
\t-vc\tVendor Class. [Option 60]
\t-V\tVendor Specific Information. [Option 43] - enter hex string.
\t-w\tOptions required in OFFER to send a REQUEST. (Comma delimited)
\t-wo\tOptions prohibited in OFFER to send a REQUEST. (Comma delim.)
\t-x\tDECLINE after DORA, ReDISCOVER count (values 0-99) (default: 0)
\t-y\tResend packets timed out awaiting response. (default: 0)
\t-ymax\tMaximum number of timeouts to retry. (default: 1000)
\t-z\tTime in seconds, to wait for server response. (default: .5)
\t-zz\tConsecutive timeouts before cluster is terminated. (default: 2) 
\t-Z\tTime in seconds, between each test cluster. (default: 0)
\t-ZZ\tTime in seconds, between each trial. (default: 0)

END_USAGE
exit;
}


## 1st Stage Main Loop
## Sucking in the Options...
############################
while($#ARGV >= 0) {
  ARG_SWITCH: {
    if ($ARGV[0] =~ /^-[a|A|H|m]$/) {
	    my $specMac;
	if ($ARGV[1] =~ /^zero$/) {
		$ch_prefix="000000";
		$ch_suffix="000000";
		$chaddr="000000000000";
		$specMac=1;
	} elsif ($ARGV[1] =~ /^ones$/) {
		$ch_prefix="ffffff";
		$ch_suffix="ffffff";
		$chaddr="ffffffffffff";
		$specMac=1;
	} elsif ($ARGV[0] =~ /^-a$/) {
	  $ch_suffix = $ARGV[1];
	  if ($ch_suffix < 1 || $ch_suffix > 16777215) {
	    $ch_suffix = 1;  
  	  }
          $ch_suffix=sprintf("%06x",$ch_suffix);
        } elsif ($ARGV[0] =~ /^-A$/) {
          $ch_suffix = $ARGV[1];
	  while (length($ch_suffix) > 6) { chop($ch_suffix);}
          while (length($ch_suffix) < 6) { 
            $ch_suffix = "0" . $ch_suffix;
          }	
        } elsif ($ARGV[0] =~ /^-m$/) {
	  $ch_prefix = $ARGV[1];
	  while (length($ch_prefix) > 6) { chop($ch_prefix);}
          while (length($ch_prefix) < 6) { $ch_prefix .= "0";}		
        } else {
          $chaddr = substr($ARGV[1],0,12);
          if ((length($chaddr) == 1)||
              (length($chaddr) == 2)||
              (length($chaddr) == 4)) {
            while (length($chaddr) < 12) { 
              $chaddr .= $chaddr;
            }
            $chaddr = substr($chaddr,0,12); 
         } else {
            while (length($chaddr) < 12) { $chaddr .= "0";}
          }
          $ch_prefix=substr($chaddr,0,6);	  
          $ch_suffix=substr($chaddr,6,6);
        }	
        if (($chaddr eq "000000000000")||
            ($chaddr eq "ffffffffffff")) {
		 if (!$specMac) {
          		$ch_suffix="000001";
          		$chaddr = $ch_prefix . $ch_suffix;
		}
        }
        shift(@ARGV); shift(@ARGV);
        last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-b$/) {
	shift(@ARGV);	$initialType = "BootP REQUEST";
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-bf$/) {
         shift(@ARGV);
	 $bootFile = &str2hex(shift(@ARGV));
	 last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-B$/) {
	shift(@ARGV);	$initialType = "Bad Packet";
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-c$/) {
	shift(@ARGV);	$ciaddr = shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-cat$/) {
        $opt81Long=1;	$opt250long=1; shift(@ARGV);   last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-C$/) {
	shift(@ARGV);	$numberOfMsgBunch = shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-d$/) {
	shift(@ARGV);		
	$discs = shift(@ARGV);
	if ($discs < 1 ){
          $discs = 1
        } elsif ($discs > 16777215) {
	  $discs = 1
	}
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-D$/) {
	shift(@ARGV);	$opt15=shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-[e|E]/) {
        if ($ARGV[0] eq '-es')
        {
            $expected_server=$ARGV[1];
            shift(@ARGV);       shift(@ARGV);   last ARG_SWITCH;
        }
        else
        {
	    $fqdn_hostname=$ARGV[1];
	    if ($ARGV[0] =~ /^-e/) {
	      $fqdn_domain="noDomainName";
	    } else {
              if ($ARGV[1] =~ /\./){
                $fqdn_hostname = $`;
                $fqdn_domain = $';
              } else {
	        $fqdn_domain="noDomainNameIncrement";
              }
            }
	    if ($ARGV[0] =~ /(\d*)$/) {
              $opt81flag=$1;
            }
	    shift(@ARGV);	shift(@ARGV);	last ARG_SWITCH;
        }
    }
    if ($ARGV[0] =~ /^-f$/) {
      shift(@ARGV);	
      $logfile = shift(@ARGV);
      open LOG, ">>$logfile";		
      last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-file$/) {
      shift(@ARGV);	$inFile = shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-F$/) {
	shift(@ARGV);			
	$foserver = shift(@ARGV);
	push (@serverArray,$foserver);
 
 last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-g$/) {
	shift(@ARGV);	
	$giaddr=shift(@ARGV);	
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^(-h|-\?)$/) { &usage; }
    if ($ARGV[0] =~ /^-i$/) {
	shift(@ARGV);
	$inform=shift(@ARGV);	
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-if$/) {
	    shift(@ARGV);
	    $specificInterface=shift(@ARGV);
	    if ($specificInterface !~ /\d+\.\d+\.\d+\.\d+/) {
		    # assume that this is an interface name and convert it to an ip
		    my $if = $specificInterface;
		    my $s = IO::Socket::INET->new(Proto => 'udp');
		    $specificInterface=$s->if_addr($if);
		    if (!$specificInterface) {
			    die "Interface $if not found\n";
#			    print STDOUT "Interface $if was not found; ";
#			    $specificInterface=&myIP;
#			    print STDOUT "binding to $specificInterface instead.\n";
		    }
		    else
		    {
			    print "Using interface $if\n";
		    }
	    }
#	    $giaddr=$specificInterface;
	    last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-I/) {
        if ($ARGV[0] =~ /^-Icisco$/) {
          $optionTerminator="00";
        }
	if ($ARGV[0] =~ /^-I1$/) {
		$o82_1 = $ARGV[1];
		chomp $o82_1;
		if (length($o82_1)%2>0){
			$o82_1="0".$o82_1;
		}
		$opt82 = 1;
	}
	if ($ARGV[0] =~ /^-I2/) { 
		$o82_2 = $ARGV[1];
		chomp $o82_2;
		if (length($o82_2)%2>0){
			$o82_2="0".$o82_2;
		}
		$opt82 = 1;
	}
	if ($ARGV[0] =~ /^-I4$/) {
		$o82_4  = $ARGV[1];
		$opt82 = 1;
	}
	if ($ARGV[0] =~ /^-I5$/) {
		$o82_5 = $ARGV[1];
		$opt82 = 1;
	}
	if ($ARGV[0] =~ /^-I6$/) {
		$o82_6 = $ARGV[1];
		$opt82 = 1;
	}
	if ($ARGV[0] =~ /^-I9$/) {
		$o82_9 = $ARGV[1];
		chomp $o82_9;
		if (length($o82_9)%2>0){
			$o82_9="0".$o82_9;
		}
		$opt82 = 1;
	}
	if ($ARGV[0] =~ /^-I11$/) {
	        $o82_11 = $ARGV[1];
	        $opt82 = 1;
	        }
	shift(@ARGV);	shift(@ARGV);	last ARG_SWITCH;
    } 
    if ($ARGV[0] =~ /^-j$/) {
	shift(@ARGV);	$fileLogging=shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-k$/) {
	shift(@ARGV); 
        if ($ARGV[0] == 0) {
        	$nack=0;
        } else {
		$nack=1;
	}
	shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-K$/) {
	shift(@ARGV);
	$opt250=shift(@ARGV);
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-l$/) {
	shift(@ARGV);
        $release=1; 
        if ($ARGV[0]==2){
          $release = 2;
        } elsif ($ARGV[0]==3){
          $release = 3;
        } elsif ($ARGV[0]==4){
          $release = 4;
        } elsif ($ARGV[0]==5){
          $release = 5;
        }			
	shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-lc$/) {
	shift(@ARGV);
	$releaseN=shift(@ARGV);
	if (($releaseN < 1)||($releaseN > 99)){
          $releaseN=1;
        } 		
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-L$/) {
	shift(@ARGV);
        if ($ARGV[0] =~ /^[i|I]/) { 
          $opt51 = 4294967295; 			
	} elsif (($ARGV[0] < 1)||($ARGV[0] > 4294967295)) { 
          $opt51 = 3600; 
        } else {
          $opt51 = $ARGV[0];
        }
	shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-LQ$/) {
	shift(@ARGV);   $initialType = "DHCP LEASE QUERY";
        $dhcpLeaseQueryType = shift(@ARGV);
	if ($dhcpLeaseQueryType eq "ip") {
	   ## CIADDR = nextparameter
	   $ciaddr = shift(@ARGV);
	} else {
	   ## CHADDR = nextparameter
	    $chaddr = substr($ARGV[0],0,12);
	    if ((length($chaddr) == 1)||
	        (length($chaddr) == 2)||
	        (length($chaddr) == 4)) {
	        while (length($chaddr) < 12) {
		  $chaddr .= $chaddr;
		}
		$chaddr = substr($chaddr,0,12);
	    } else {
		while (length($chaddr) < 12) { $chaddr .= "0";}
	    }
	    $ch_prefix=substr($chaddr,0,6);
	    $ch_suffix=substr($chaddr,6,6);
            shift(@ARGV);
        }
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-M$/) {
	shift(@ARGV);
        if ($ARGV[0] == 3) { 
          $initialType = "DHCP REQUEST"; 			
	} elsif ($ARGV[0] == 4) { 
          $initialType = "DHCP DECLINE"; 
	} elsif ($ARGV[0] == 7) { 
          $initialType = "DHCP RELEASE"; 
        } elsif ($ARGV[0] == 8)  {
          $initialType = "DHCP INFORM"; 
        } elsif ($ARGV[0] == 10) {
	  $initialType = "DHCP LEASE QUERY";
        }
	shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-[n|N]$/) {
      $hostname = $ARGV[1];
      if ($ARGV[0] =~ /^-n$/) {	
         $incHostname="";	
       } else {
         $incHostname=$hostname;
       }
      shift(@ARGV); shift(@ARGV);	
      last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-NIS$/) {
	    shift(@ARGV);	$opt40 = shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-NTRAS$/) {
	shift(@ARGV);	$initialType = "NT RAS Packet";
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-o$/) {
        shift(@ARGV);	$opt50 = shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-O$/) {
	shift(@ARGV);	$opt55 = shift(@ARGV);	last ARG_SWITCH;
    } 
    if ($ARGV[0] =~ /^-p$/) {
	shift(@ARGV);			
        $decodeOptionsServerPacket=1;
        last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-P$/) {
	shift(@ARGV);	$phone=shift (@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-q$/) {
	shift(@ARGV);	
	$screenLogging=shift(@ARGV);
	if($screenLogging==1){$progressBar=1;}
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-r$/) {
	shift(@ARGV);	$renew = shift(@ARGV);	last ARG_SWITCH;
    }    
    if ($ARGV[0] =~ /^-rc$/) {
	shift(@ARGV);
        $renewN = shift(@ARGV);
        if (($renewN < 0 )||($renewN > 99)){
           $renewN=1;
        }		
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-renew$/){
	    shift(@ARGV);
	    $ciaddr = $ARGV[0];
	    $initialType = "DHCP REQUEST";
	    $nack=0;
	    shift(@ARGV);
	    last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-rg$/){
	 shift(@ARGV);
	 if (!$ARGV[0]){
		 $renewGiaddr=0;
	 }
	 shift(@ARGV);
	 last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-R$/) {
	shift(@ARGV);	$sendOnly=1;	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-RAS2k$/) {
	shift(@ARGV);
        $initialType = "2K RAS Packet";
        last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-RC$/) {
	shift(@ARGV); $opt80=1; last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-s$/) {
	shift(@ARGV);			
	$server = $ARGV[0];
	$serverArray[0] = $server;
	shift(@ARGV);	
#        if ($giaddr eq INADDR_ANY){
#          $giaddr=&myIP;
#        }
        last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-si$/) {
	shift(@ARGV);
	$opt54=shift(@ARGV);
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-sn$/) {
        shift(@ARGV);
	$sName=&str2hex(shift(@ARGV));
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-ss$/) {
	shift(@ARGV);			
	$splitserver = shift(@ARGV);
	push(@serverArray, $splitserver);
        last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-S$/) {
	shift(@ARGV);	$opt118 = shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-t$/) {
	shift(@ARGV);		
	$outerLoop = $ARGV[0];
	shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-T$/) {
	    shift(@ARGV);
	    $outputSuppressionFactor=shift(@ARGV);
	    if ($outputSuppressionFactor =~ /\D+/) {
		    $outputSuppressionFactor=1;
	    }
	    if ($outputSuppressionFactor <= 0) {
		    $outputSuppressionFactor=1;
	    }
	    last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-u$/) {
	shift(@ARGV);
	$opt77=&str2hex(shift(@ARGV));
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-U$/) {
        shift(@ARGV);
	$opt77=&dnsEncode(shift(@ARGV));
	chop $opt77; chop $opt77;
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-v$/) { &version; }		
    if ($ARGV[0] =~ /^-vc$/) {
	shift(@ARGV);	$opt60 = shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-V$/) {
	shift(@ARGV);		
	$opt43 = shift(@ARGV);
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-x$/) {
	shift(@ARGV);
	$decline = shift(@ARGV);
        if (($decline < 0 )||($decline > 100)){
           $decline=100;
        }		
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-w$/) {
	shift(@ARGV);
        @with=split(/,/,$ARGV[0]);
	shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-wo$/) {
	shift(@ARGV);
        @without=split(/,/,$ARGV[0]);
	shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-y$/) {
	shift(@ARGV);
	$reDiscoverTimeOuts=shift(@ARGV);
        if ($reDiscoverTimeOuts != 1){
          $reDiscoverTimeOuts=0;
        } else {
          $reDiscoverTimeOuts=1;
        }
	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-ymax$/) {
	shift(@ARGV);	$reDiscTimeOutsMaxTries = shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-z$/) {
	shift(@ARGV);	$timeOutWaiting = shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-zz$/) {
	shift(@ARGV);	$timeOutGiveUp = shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-Z$/) {
	shift(@ARGV);	$waitCluster = shift(@ARGV);	last ARG_SWITCH;
    }
    if ($ARGV[0] =~ /^-ZZ$/) {
	shift(@ARGV);	$waitTrial = shift(@ARGV);	last ARG_SWITCH;
    }  
    print STDOUT "Unknown flag '$ARGV[0]'.\n";
    exit;
  }
}

## Main Program Loop
####################
if (($giaddr ne "0.0.0.0")&&($server ne "255.255.255.255")) { $local=67; } 
if (($foserver)||($splitserver)) {
	if ($server eq "255.255.255.255") {
		print STDOUT "\tPrimary DHCP Server is not set!\n";
      		exit;
    	}  
}
&setUpLoggingLevels;
if ($local==68){
	$pidFile="$0.0.0.0.0.pid";
	# Check to see if pid file exists and write it if it doesn't
	# Exit the program if pid exists.
	die "Mlease is already running in broadcast mode.\n" 
		if (-f $pidFile);
#		if hold_pid_file($pidFile);
	if (!$specificInterface) {
		die "No specific interface specified\n";
	}
	&setupLocalSocket($specificInterface);
} else {
	if (!$specificInterface) {
#		$specificInterface=&myIP
		die "No specific interface specified\n";
	}
	$pidFile="$0.$specificInterface.pid";
	# Check to see if pid file exists and write it if it doesn't
	# Exit the program if pid exists.
	die "Mlease is already running on $specificInterface!\n" 
		if (-f $pidFile);
#		if hold_pid_file($pidFile);
	&setupSocket($specificInterface);
}
my $org_options=$options;
my $org_ch_suffix=$ch_suffix;
for (my $q=1; $q <= $outerLoop; $q++){
	$discount=0;       $offcount=0;
    	$reqcount=0;       $deccount=0;
    	$ackcount=0;       $nakcount=0;
    	$relcount=0;       $infcount=0;
	$lqcount=0;        $lqunkcount=0;
	$lqunacount=0;     $lqactcount=0;
    	$bootpRequest=0;   $bootpReply=0;
    	$timeOutCounter=0; $totalTrialTime=0;
    	$badPacketCounter=0;
    	$ignoredPacketCounter=0;
    	$unexpectedPacketCounter=0;
    	print DEBUGTWO "\nTrial $q\n---------------------------------------------------\n";
    	print PROGRESS "Trial $q\n---------------------------------------\n";
    	$ch_suffix=$org_ch_suffix;
    	$options=$org_options;
    	if ($inFile) {
		my $xml = new XML::Simple;
		my $data = $xml->XMLin($inFile);
		my $filexid =  $data->{global}->{xid};
		my $fileciaddr =  $data->{global}->{ciaddr};
		my $fileyiaddr =  $data->{global}->{yiaddr};
		my $filesiaddr =  $data->{global}->{siaddr};
		my $filegiaddr =  $data->{global}->{giaddr};
		my $filechaddr =  $data->{global}->{chaddr};
		my $filemessagetype =  $data->{global}->{type};
		my $fileserver =  $data->{global}->{server};
		my $fileoptions =  $data->{global}->{options};
		foreach my $e (@{$data->{client}}){
		        if ($e->{xid}){
		                push (@agenda, $e->{xid});
		        } else {
		                push (@agenda, $filexid);
		        }
		        if ($e->{ciaddr}){
		                push (@agenda, $e->{ciaddr});
		        } else {
			        push (@agenda, $fileciaddr);
	 	        }
			if ($e->{yiaddr}){
			        push (@agenda, $e->{yiaddr});
			} else {
			        push (@agenda, $fileyiaddr,);
			}
			if ($e->{siaddr}){
			        push (@agenda, $e->{siaddr},);
			} else {
			        push (@agenda, $filesiaddr);
			}
			if ($e->{giaddr}){
			        push (@agenda, $e->{giaddr});
			} else {
			        push (@agenda, $filegiaddr);
			}
			if ($e->{chaddr}){
			        push (@agenda, $e->{chaddr});
			} else {
			        push (@agenda, $filechaddr);
			}
			if ($e->{type}){
			        push (@agenda, $e->{type});
			} else {
			        push (@agenda, $filemessagetype);
			}
			if ($e->{server}){
			        push (@agenda, $e->{server});
			} else {
			        push (@agenda, $fileserver);
			}
			if ($e->{options}){
			        push (@agenda, $e->{options});
			} else {
			        push (@agenda, $fileoptions);
			}
			$clientOptions{$agenda[-4]}=$agenda[-1];
		}
		#open(DAT, "<$inFile");
		#my(@lines) = <DAT>;
		# my($line);
		#foreach my $line (@lines){
			#	chomp $line;
			#push (@agenda, split(/,/, $line));
			# $agenda[-3]=verifyMsgType($agenda[-3]);
			# if ($agenda[-3] eq "NT RAS Packet"){
			#          $agenda[-4]=verifyMacAddr("52415320".$agenda[-4], 16);
			# }  else {
			#	$agenda[-4]=verifyMacAddr($agenda[-4]);
			# }
			# $clientOptions{$agenda[-4]}=$agenda[-1];
			# } 
			# close(DAT);
    	} else {
      		for (my $i=1; $i <= $discs; $i++){
        		my $xid;
        		if ($decline) {
          			if ($decline-100){
            				$xid = "dddd".sprintf("%02d", int(rand(99))).sprintf("%02d", $decline);
          			} else {
            				$xid = "dddd".int(rand(9)).sprintf("%02d", $decline);             
          			}
        		} elsif ($inform) {
				$xid = "cccc".sprintf("%02d", int(rand(99))).sprintf("%02d", $inform);
			} elsif ($renew) {
            			$xid = "bbbb".$renew.int(rand(9)).sprintf("%02d", $renewN);
      			} elsif ($release) {
            			$xid = "eeee".$release.int(rand(9)).sprintf("%02d", $releaseN);
        		} else {
          			$xid = sprintf("%08d", int(rand(94967294)));
        		}
        		$chaddr=$ch_prefix.$ch_suffix;
        		#### Client Side Options ####
			if (!$opt81flag){
        		    if ($incHostname){
          			$options .= &option_packer(12,"$hostname-$ch_suffix");
        		    } else {
          			$options .= &option_packer(12,"$hostname");
        		    }
        		    if ($opt15) {
          			$options .= &option_packer(15,"$opt15");
        		    }
		        }
			if ($opt40) {
				$options .= &option_packer(40,"$opt40");
			}
        		if ($opt43) {
          			$options .= &option_packer(43,"$opt43");
        		}
        		if ($opt51) {
          			$options .= &option_packer(51, sprintf("%08x", $opt51));
        		}
			if ($opt54) {
				$options .= &option_packer(54,"$opt54");
			}
        		if ($opt55) {
          			$options .= &option_packer(55,"$opt55");
        		}
        		if ($opt60) {
          			$options .= &option_packer(60,"$opt60");
        		}
        		if ($opt77) {
          			$options .= &option_packer(77,"$opt77");
        		}
        		if ($fqdn_hostname) {
				my $fqdn=$fqdn_hostname;
				if ($fqdn_domain eq "noDomainNameIncrement"){
					$fqdn.="-$ch_suffix";
					$fqdn_domain="noDomainName";
				}
				if ($fqdn_domain !~ /^noDomainName$/) {
					$fqdn.="-$ch_suffix.$fqdn_domain";
				}
				if ($opt81flag) {
					$fqdn = &dnsEncode($fqdn);
				}
				if ($opt81Long) {
					my $fqdnHalf = length($fqdn)/2;
					if (($fqdnHalf % 2) == 1) {$fqdnHalf++;}
					my $fqdn_front = substr($fqdn,0,$fqdnHalf);
					my $fqdn_back = substr($fqdn,$fqdnHalf);
					if (!$opt81flag) {$fqdn_back=&str2hex($fqdn_back);}
					$options .= &option_packer(81,$fqdn_front);
					$options .= "51";
					$options .= &dec2hex(length($fqdn_back)/2);
					$options .= $fqdn_back;
				} else {
					$options .= &option_packer(81,$fqdn);
				}
			}
        		if ($opt118) {
          			$options .= option_packer(118,"$opt118");
        		}
			if ($opt250) {
				if ($opt250long){
					my $opt250Half = length($opt250)/2;
					if (($opt250Half % 2) == 1) {$opt250Half++;}
					my $opt250_front = substr($opt250,0,$opt250Half);
					my $opt250_back = substr($opt250,$opt250Half);
					$options .= option_packer(250,"$opt250_front");
					$options .= option_packer(250,"$opt250_back");
				} else {
					$options .= option_packer(250,"$opt250");
				}
			}
        		### Options above are echoed in the REQUEST           
        		$clientOptions{$chaddr}=$options;
        		### Options below are not echoed in the REQUEST
        		if ($opt50){
          			$options .= &option_packer(50, $opt50);
        		}
			if ($opt80){
				$options .= "5000";
			}
			if ($opt82){
				if ($o82_1) {
					if ($o82_1 != 1) {
						$o82 = &option_packer(43, $o82_1);
						$o82 = "01" . substr($o82,2);
					} else {
						my $ch_suffix1 = substr($ch_suffix,2);
						if (($ch_suffix1 =~ '27$')||($ch_suffix1 =~ '^27')) {
							$ch_suffix1 = "0000";
						}
						#option 82 suboption 1 in normal padding format
						$o82 = "01060004564c" . $ch_suffix1 
					}
				}
				if ($o82_2) {
					if ($o82_2 != 1) {
						$o82_2 = &option_packer(43, $o82_2);
						$o82 .= "02" . substr($o82_2,2);
					} else {
						#option 82 suboption 2 in normal padding format
						$o82 .= "02080006" . $ch_suffix . $ch_prefix;
					}
				}
				if ($o82_4){
					$o82 .= "0404" . sprintf('%08x', $o82_4); 
				}
				if ($o82_5){
					$o82 .= "0504" . unpack("H8",&inet_2_hex($o82_5));
				}
                                if ($o82_6){
					 my $o82_6temp = &option_packer(60, $o82_6);
				        $o82 .= "06" . substr($o82_6temp,2);
			        }
				if ($o82_9){
					my $o82_9temp = &option_packer(43, $o82_9);
					$o82 .= "09" . substr($o82_9temp,2);
				}
				if ($o82_11){
			                $o82 .= "0b04" . unpack("H8",&inet_2_hex($o82_11));
									                                }
				$o82 =  &option_packer(82, $o82);
				$options .= $o82;
				$clientOptions{$chaddr}.=$o82;
				$o82="";
				$o82len = length($o82);
	 		}
        		$ch_suffix = &inc_mac($ch_suffix);
        		my $type=$initialType;
        		push (@agenda, ($xid,$ciaddr,$yiaddr,$siaddr,$giaddr,$chaddr,$type,$server,$options));
        		$options="";
      		}
    	}
    	my $tt0=time;
    	while (@agenda) {
      		for (my $j=1; $j <= $numberOfMsgBunch; $j++){
        		push (@toDoList, splice(@agenda, 0, 9));
        		if (!$agenda[0]){
          			last;
        		}
      		}
      		my $t0=time;
      		while (@toDoList) {
        		&sendReceive;
        		push (@toDoList, @actionItems);
        		@actionItems=();
      		}
      		my $t1=time;
      		my $et=sprintf("%02.3f",$t1-$t0);
      		$totalTrialTime+=$et;
      		print PROGRESS "\n  This Cluster used $et seconds.\n";
      		print DEBUGTWO "  This Cluster used $et seconds.\n\n";
      		sleep($waitCluster);
    	}
    	$totalDisCount+=$discount;		$totalOffCount+=$offcount;
    	$totalReqCount+=$reqcount;		$totalAckCount+=$ackcount;
    	$totalInfCount+=$infcount;		$totalNakCount+=$nakcount;
    	$totalRelCount+=$relcount;		$totalDecCount+=$deccount;
	$totalLqCount+=$lqcount;                $totalLqunkCount+=$lqunkcount;
	$totalLqunaCount+=$lqunacount;          $totalLqactCount+=$lqactcount;
    	$totalBpReqCount+=$bootpRequest;	$totalBpRepCount+=$bootpReply;
    	$totalTimeOutCount+=$timeOutCounter;
    	$totalBadPacketCount+=$badPacketCounter;
    	$totalIgnoreCount+=$ignoredPacketCounter;
    	$totalUnexCount+=$unexpectedPacketCounter;
    	$totalRunTime+=$totalTrialTime;
	if ($screenLogging >= 2 ) {
		$outputSuppressionFactor=1;
	}
	if (($outerLoop == 1) || ($q % $outputSuppressionFactor == 0)) {
		if ($outerLoop > 1) {
			print DEBUGONE "  ---------------------------\n";
			printf DEBUGONE "  -- Summary for Trial %5d\n" ,$q;
		} else {
			print DEBUGONE "  ---------------------------\n";
			print DEBUGONE "  -- Summary  for this  test\n";
		}
    		print DEBUGONE "  ---------------------------\n";
	    	printf DEBUGONE "  %-15s : %u\n", "DHCP Discovers", $discount if $discount;
                printf DEBUGONE "  %-15s : %u\n", "DHCP Offers", $offcount if $offcount;
    		printf DEBUGONE "  %-15s : %u\n", "DHCP Requests", $reqcount if $reqcount;
                printf DEBUGONE "  %-15s : %u\n", "DHCP Acks", $ackcount if $ackcount;
	    	printf DEBUGONE "  %-15s : %u\n", "DHCP Informs", $infcount if $infcount;
                printf DEBUGONE "  %-15s : %u\n", "DHCP Nacks", $nakcount if $nakcount;
    		printf DEBUGONE "  %-15s : %u\n", "DHCP Releases", $relcount if $relcount;
                printf DEBUGONE "  %-15s : %u\n", "DHCP Declines", $deccount if $deccount;
		printf DEBUGONE "  %-15s : %u\n", "DHCP LQ", $lqcount if $lqcount;
                printf DEBUGONE "  %-15s : %u\n", "DHCP LQ Unknown", $lqunkcount if $lqunkcount;
		printf DEBUGONE "  %-15s : %u\n", "DHCP LQ Unass.", $lqunacount if $lqunacount;
                printf DEBUGONE "  %-15s : %u\n", "DHCP LQ Active", $lqactcount if $lqactcount;
	    	printf DEBUGONE "  %-15s : %u\n", "BootP Requests", $bootpRequest if $bootpRequest;
                printf DEBUGONE "  %-15s : %u\n", "BootP Replies", $bootpReply if $bootpReply;
    		printf DEBUGONE "  %-15s : %u\n", "Time Outs", $timeOutCounter if $timeOutCounter;
                printf DEBUGONE "  %-15s : %u\n", "Bad Packets", $badPacketCounter if $badPacketCounter;
	    	printf DEBUGONE "  %-15s : %u\n", "Ignored Pkts.", $ignoredPacketCounter if $ignoredPacketCounter;
                printf DEBUGONE "  %-15s : %u\n", "Unexp. Packets", $unexpectedPacketCounter if $unexpectedPacketCounter;
    		print DEBUGTWO "  This trial used ".sprintf("%02.3f",$totalTrialTime)." seconds.\n\n";
                if (($dhcppacket[1] =~ /\./) && $decodeOptionsServerPacket){
		  print DEBUGONE "  -----------------------\n";
		  print DEBUGONE "  -- Last packet details:\n";
    		  print DEBUGONE "  -----------------------\n";
                  print DEBUGONE "  xid       : $detailpacket[0]\n";
                  print DEBUGONE "  ciAddr    : $detailpacket[1]\n";
	          print DEBUGONE "  yiAddr    : $detailpacket[2]\n";
	          print DEBUGONE "  siAddr    : $detailpacket[3]\n";
	          print DEBUGONE "  giAddr    : $detailpacket[4]\n";
	          print DEBUGONE "  chAddr    : $detailpacket[5]\n";	  
	          print DEBUGONE "  sname     : $detailpacket[6]\n";	  
	          print DEBUGONE "  bootfile  : $detailpacket[7]\n";	  
                  &decodeOptions($detailpacket[8]);
                }
	}
    	sleep($waitTrial);
}

if ($outerLoop == 1) { exit; }

## Summary of Entire Run.
#########################
$discount=$totalDisCount;           $offcount=$totalOffCount;
$reqcount=$totalReqCount;           $ackcount=$totalAckCount;
$infcount=$totalInfCount;           $nakcount=$totalNakCount;
$relcount=$totalRelCount;           $deccount=$totalDecCount;
$lqcount=$totalLqCount;             $lqunkcount=$totalLqunkCount;
$lqunacount=$totalLqunaCount;       $lqactcount=$totalLqactCount;
$bootpRequest=$totalBpReqCount;     $bootpReply=$totalBpRepCount;
$timeOutCounter=$totalTimeOutCount; $badPacketCounter=$totalBadPacketCount;
$ignoredPacketCounter=$totalIgnoreCount;
$unexpectedPacketCounter=$totalUnexCount;

#print DEBUGONE "----------------\nSummary for Run:\n----------------\n";
#print DEBUGONE "DHCP Discovers $discount\tDHCP Offers     $offcount\n";
#print DEBUGONE "DHCP Requests  $reqcount\tDHCP Acks       $ackcount\n";
#print DEBUGONE "DHCP Informs   $infcount\tDHCP Nacks      $nakcount\n";
#print DEBUGONE "DHCP Releases  $relcount\tDHCP Declines   $deccount\n";
#print DEBUGONE "DHCP LQ        $lqcount \tDHCP LQ Unknown $lqunkcount\n";
#print DEBUGONE "DHCP LQ Unass. $lqunacount\tDHCP LQ Active  $lqactcount\n";
#print DEBUGONE "BootP Requests $bootpRequest\tBootP Replies   $bootpReply\n";
#print DEBUGONE "Time Outs      $timeOutCounter\tBad Packets     $badPacketCounter\n"; 
#print DEBUGONE "Ignored Pkts.  $ignoredPacketCounter\tUnexp. Packets  $unexpectedPacketCounter\n";
#print DEBUGONE "\tThis Run used ".sprintf("%02.3f",$totalRunTime)." seconds.\n\n";

print DEBUGONE "----------------\nSummary for Run:\n----------------\n";
printf DEBUGONE "%-15s : %u\n", "DHCP Discovers", $discount if $discount;
printf DEBUGONE "%-15s : %u\n", "DHCP Offers", $offcount if $offcount;
printf DEBUGONE "%-15s : %u\n", "DHCP Requests", $reqcount if $reqcount;
printf DEBUGONE "%-15s : %u\n", "DHCP Acks", $ackcount if $ackcount;
printf DEBUGONE "%-15s : %u\n", "DHCP Informs", $infcount if $infcount;
printf DEBUGONE "%-15s : %u\n", "DHCP Nacks", $nakcount if $nakcount;
printf DEBUGONE "%-15s : %u\n", "DHCP Releases", $relcount if $relcount;
printf DEBUGONE "%-15s : %u\n", "DHCP Declines", $deccount if $deccount;
printf DEBUGONE "%-15s : %u\n", "DHCP LQ", $lqcount if $lqcount;
printf DEBUGONE "%-15s : %u\n", "DHCP LQ Unknown", $lqunkcount if $lqunkcount;
printf DEBUGONE "%-15s : %u\n", "DHCP LQ Unass.", $lqunacount if $lqunacount;
printf DEBUGONE "%-15s : %u\n", "DHCP LQ Active", $lqactcount if $lqactcount;
printf DEBUGONE "%-15s : %u\n", "BootP Requests", $bootpRequest if $bootpRequest;
printf DEBUGONE "%-15s : %u\n", "BootP Replies", $bootpReply if $bootpReply;
printf DEBUGONE "%-15s : %u\n", "Time Outs", $timeOutCounter if $timeOutCounter;
printf DEBUGONE "%-15s : %u\n", "Bad Packets", $badPacketCounter if $badPacketCounter;
printf DEBUGONE "%-15s : %u\n", "Ignored Pkts.", $ignoredPacketCounter if $ignoredPacketCounter;
printf DEBUGONE "%-15s : %u\n", "Unexp. Packets", $unexpectedPacketCounter if $unexpectedPacketCounter;
print DEBUGTWO "  This Run used ".sprintf("%02.3f",$totalRunTime)." seconds.\n\n";

1;

__END__

=head1 MLease

The Art of DHCP Testing.

=head2 Change History

=head3 2.0.1 08-31-2009

=over

=item

Based off of 1.4.2

=item

Removed Interface, Proc, Tie, and XML modules.

=item

Added additional listening socket when doing broadcast

=item

Added '-es <server>' option to skip answers from other servers (useful in broadcast testing

=back

=head3 1.4.0 10-23-2007

=over

=item

Corrected problem with Option 81 concatination.  Option 81 can be concatinated
in both its draft 0 and draft 13 incarnations.

=item

Added option 250.  This is a concatination enabled option as well as 
option 81.  The "-cat" flag will enable concatination for both options and
the "-K" flag will allow a hex input string to be entered for option 250.

=item 

Option 82 flags were serperated out.  There is not dependancies on any suboption
flag.  All option 82 suboptions are now independant.

=item

Option 82 Suboptions 1 and 2 were formatted more realistically according to a 
document by H3C.  The URL is:
http://www.h3c.com/protal/Products___Solutions/Technology/IPv4___IPv6_Services/DHCP/200701/195562_57_0.htm
Suboption 1 is not 6 bytes in length and contains a 1 byte Circuit ID type (x00)
A length byte (x04), a two byte VLAN ID (x564c) and a two byte interface number.
Suboption 2 is not length 8 and contains a remote ID type of (x00) and a length
byte of (x06).  The remainder of the six bytes are a shuffling of the client's
MAC address.

=item

Added more decoding for the -p packet decode flag.  In particular IP address and 
String option decodes.

=back

=head3 1.3.9 4-4-2007

=over 

=item

Fixed a problem with option 82 being malformed with the change made in 
MLease 1.3.8.

=back

=head3 1.3.8 1-22-2007

=over

=item

Changed the size of the mac_prefix to 6 and the mac_suffix to 6 so that MLease 
can simulate more (16777215) clients on the command line.

=back

=head3 1.3.7 12-29-2006

=over

=item

Added Option 82 Suboption 9.

=back

=head3 1.3.6 07-03-2006

=over

=item

Changed the -P flag to accept any number of digits and not 
the 10 digits that were hardcoded.  This means that the -P
flag can be used to represent a phone number or an ip 
address in hex.

=back

=head3 1.3.4 04-28-2006

=over

=item

Changed the input file format from csv to xml.  This 
eliminates some of the problems that existed in the 
csv implementation.  The XML::Simple module saved me from
writting a parser from scratch.  Now null values can now 
be placed in the agenda array.

=item

Reworked the decline logic so that the hot xid ddddxx00
will send only a decline and not close down the socket.
There is a problem with the "-x 0" flag.  it does not 
issue a decline.  This is an existing bug and should be 
repaired in a future release.

=back

=head3 1.3.3 04-27-2006

=over

=item

Fixed a problem with the Lease Query Options list being 
placed after the option terminator.

=item 

Added a chomp to remove the end of line character from 
the options list.  The positive of this addition is that
options do not have an extra "A0" in the data stream.  
The down side is that the options section of the input
file is no longer able to be empty.

=back

=head3 1.3.2 04-21-2006

=over

=item

Fixed the canned input file functionality.  MLease will now 
work off of a scripted input file.

=item

Fixed a logic problem that caused the bad packet generator and
the NT and Win2K RAS packet generators to stop working.  This 
bug was introduced in 1.2.9.

=item

A bug was reported with the "-U" option.  Userclasses ending 
with a zero in the label were being truncated.  The length on
the other had did not reflect this truncation.  The dnsEncode
subroutine was rewritten and the problem corrected.

=item

Two subroutines were created in order to more efficiently convert
strings to hex (str2hex) and decimal to hex (dec2hex).  Some of 
the convoluted code to do these things was replaced with these 
routines.  Many of the sprintf calls, over half, were replaced with 
the above mentioned subroutines.

=back

=head3 1.3.1 04-14-2006

=over

=item

Added support for the RFC 3004 version of User Class.  I reused the 
DNS Encoding routine to accomplish this.  The new flag is "-U" and
it accepts multiple user classes delimited by periods.

=item

Added support for option 80, the Rapid Commit Option RFC 4039.  I do 
not have a DHCP server to test its effectiveness, but it should only 
send this option in the DISCOVER and not the REQUEST.  MLease should 
also accept an ACK instead of the OFFER.

=back

=head3 1.3.0 04-11-2006

=over

=item

Added support for the four new message types specified in RFC 4388.  
This is the Lease Query messaging.  The client sends the server a 
Lease Query Message and will receive one of there responses depending
on the situation.  Those responses are LQ Unknown, LQ Unassigned and
LQ Active if there is an active lease that fits the criteria.  The 
new "-LQ" flag takes two parameters.  The first is a query type and 
valid values are ip, mac, id.  The second parameter is an IP address
or MAC address depending on the context of the first parameter.  New 
counters were added and both the mac and client-id querying methods 
are incrementing.

=back

=head3 1.2.9 04-06-2006

=over

=item

Added support for draft-ietf-dhc-fqdn-option-13.txt implementation of
option 81.  The -e/-E flags have become the -en/-En flags where n is the 
numeric representation of the encoding flags, typically this value will be
4.  A value of zero for the flags will cause MLease to simulate a client 
that implements draft zero (draft-ietf-dhc-fqdn-option-0.txt)

=item

Added -cat flag which will allow the above option 81 draft 13 to be sent
as a concatinated option.

=back

=head3 1.2.8 03-22-2006

=over

=item

Fixed the problem where multiple informs would not populate the CIAddr field.

=item

Fixed the problem with the BootP counter Incrementing.

=back

=head3 1.2.7 10-13-2005

=over

=item

Added a incrementing Option 82 Circuit ID.  The Circuit ID will increment if the "-I1" flag is not used.  The "-I1" flag will override the incrementing Circuit ID and allow the user to specify a fixed Circuit ID for the test.

=back

=head3 1.2.6 04-18-2005

=over

=item

Revised the phone number logic to accept only whole phone numbers. Revised the client identifier to conform to the AT&T Wireless practice of having an ascii representation of the phone number in the option 61. 

=item

Added the ability to specify an SName.

=back

=head3 1.2.5 10-26-2004

=over

=item

Added the ability for the user to specify a bootfile name in packets 
bound for the server.  The new option is "-bf".

=back

=head3 1.2.4 09-23-2004

=over

=item

Added the ability for the user of this program to add a server identifier 
to the packet.  Specifically, this is required for selecting requests and
gives the user more flexibility when sending in renew packets.

=back

=head3 1.2.3 08-13-2004

=over

=item

Fixed issue where option 54 was not being echoed in request packet.  This was 
causing the dhcp server to incorrectly intrepret the REQUEST as an INIT-REBOOT
attempt.  When the Address Shuffling policies were set, the server would 
continually NACK the REQUEST.

=back

=head3 1.2.2 06-23-2004

=over

=item

All the mac address option flags, a, A, H and m now accept the keywords "one" 
and "zero".  One will set the mac address for one trial to "ffffffffffff" and 
zero will set the mac address to "000000000000".

=item

The client can now send option 40, although that option is typically not sent.

=back

=head3 1.2.1 03-24-2004

=over

=item

The name and location of the pid file were changed.  The name and 
location of the PID will be determined by $0.

=item

All prints that were directed to STDERR were redirected back to STDOUT.
This change was made so the JBots would report any errors that mlease
would generate instead of sending a blank message.

=item 

I added an option that would suppress a variable amount of trial summary
data.  This is useful for bursts of repeated quick transactions.  The new
flag is -T and it accepts a numeric argument.  This trial number is modulod
by this argument and will only print when the result is zero.  The default
for this flag is one.  The flag only applies to screen Debug 0 and 1.

=item

Cleaned up extraneous comments and code.

=back

=head3 1.2.0 03-22-2004

=over

=item

The Change History was removed from the front of the file as a series of
comments and placed at the end of the file in POD.

=item

I decide to split MLease in two trees, one for Linux and one for Windows.
The reason for this break is the unavailability of IO::Interface module
for Windows.  Both trees will be designated by the operationg sustem.
The main difference will be that thee Windows tree will have the 
IO::Interface section commented out.  I was going to discontinue support
for Win32 altogether, but saw a need for MLease to run on Windows and 
fix problems like the Option 82 below.

=item

The Debug levels needed to be revised to reflect the changes needed to 
package this data and present it through the JBots.  The model for the 
Debug levels is as follows:  Debug Three will collect packet diagrams,
play by play transaction descriptions, and summary information.  Debug
Two will collect the play by play transaction descriptions and the 
summary informtation.  Debug One to the log will be just the summary 
information and Debug One to STDOUT will be the summary information and 
the Progress indicator.  Debug Zero will be the new default and will only
print the summary information to STDOUT.  Debug Zero is not available in
a logfile.

=item

Added routines to write the pid files.  Since MLease can bind and run tests
on individual NICs on a multiNIC box, there was a need to distingish which 
interface was in use in the pad file.  I decided to incorporate the ip 
address in the pid filename.  When MLease starts, it checks for a existing
pid file before binding to the socket.  If the pid file exists and the 
process is still running, MLease will exit.

=back

=head3 1.1.4 03-19-2004 

=over 

=item 

Unbuffered the output in order to make Mlease work better with the Jbots.  
This will allow the Jbots to report progress more accurately.

=item 

Corrected a problem with option 82 suboption 2.
The problem was that this unique identifier was being corrupted by the 
use of the $o82 variable as a temp and for the length of the entire 
option.  This did not work as $o82 needs to be reset when generating 
more than one discover packet.  There also was a problem with Option 82 
suboption 2 being duplicated in QIP.  This now appears to be a QIP problem
as testing and packet traces show that MLease is doing the right thing now.

=back

=head3 1.1.3 03-11-2004 

=over

=item 

Removed the random send port "-rsp" flag which essentially did nothing 
with the updated socket subroutines.

=item

Added a check that verifies the unicast socket is not being set to 
localhost.

=item

Added code that allows the user to specify the network interface which 
will run the test.  The user can specify the interface by name or by 
IP address.

=item

Reworked the logs to minimize the logging output to speed up the client's 
performance when being executed by jbot2 (Whacker 4).

=back

=head3 1.1.2 02-12-2004 

=over

=item

Fixed the "-R" flag, the input loop had a typo.

=back

=head3 1.1.1 01-21-2004 

=over

=item

Revision of DHCP option 82 to include additional suboptions 4 and 5.

=back

=head3 1.1.0 01-21-2004

=over

=item 

Implementation of the broadcast listening socket for server values 
of 255.255.255.255 and GIAddr values of 0.0.0.0.  The sending of 
Broadcast packets will work with single NIC computers.  Dual NIC
boxes can send broadcast packets, but will not listen to them.  
This limitation does not affect the dual NIC box's ability to 
unicast traffic, which will account for over 90% of the testing
we do.

=item

Implementation of the broadcast of packets when the server value 
is 255.255.255.255.  This has been the default behavior of the client,
unfortunately, it has not worked until now.

=back

=head3 1.0.b 01-20-2004 

=over

=item

Experimentation with capturing packets off the broadcast sockets.

=back

=head3 1.0.a 01-14-2004

=over

=item

Cleaned up an extra carriage return in help screen.

=item

The "-P" option displays the value of the option in the progress bar.

=item

The bad packet counter did not increment correctly. this problem was 
corrected.

=item

Inserted a counter to capture unexpected responses and another counter 
to capture packets that MLease ignored as duplicates or responses from
a split scope server.

=item

Added a formal renew option.  In this process, the code that specifies 
whether to use a GIAddr during a renew is suspect and needs to be looked
at.  The code as written will count RENEWs with no GIAddr as time outs 
when they should not be counted at all.

=back

=head3 1.0.9 01-09-2004

=over

=item

Began cleaning up extraneous comments from the code.

=item

Put in a cumulative statistic counters for long runs containing high 
values for "-t".

=item

Suppressed the printing of packet headers for timed out packets.

=back

=head3 1.0.8 01-08-2004 

=over

=item

Muhammad came up with the solution to make the attempted modifications 
in 1.0.7 work.  Namely, we can specify a destination in the send
routine, instead of specifying the send to destination when we set up 
the socket.  This will overcome the windows issue mentioned below and 
allow multiple sends on all platforms.

=item

Extraneous subroutines were gutted in light of this elegant solution.

=back

=head3 1.0.7 01-07-2004

=over
 
=item

Modified the listen routine so the it will be more robust when dealing 
with failover servers under the windows OS.  v1.0.6 worked correctly
under linux.  The experience gained in this attempted modification 
revealed that the problem with windows is with the select module.

=back

=head3 1.0.6 01-02-2004 

=over

=item

Modified the listen routine so that it will not terminate the program 
if the DHCP box sends a port unavailable message instead of an OFFER 
or other valid response.

=item

Revised the Option 82 Routine to do the following: accept a circuit id 
from the user and append the iteration number to the circuit id.  The
remote id is the ch_suffix followed by the ch_prefix - basically a 
shuffled mac address. Note: there is no error checking in this routine,
so it is possible to have the remote id equal the dhcp client mac address.

=item

Made corrections to the help screen.

=back

=head3 1.0.5 10-09-2003 

=over

=item

Revised the packet decode routine.  It is now more robust.  I also added 
the printable ascii decode on the side.

=item

Changed error in help screen replaced RELEASE with RENEW.

=item

Revised the option decode routine to also display the ciaddr, yiaddr, 
siaddr, giaddr and chaddr.

=item

Added an flag to allow or disallow GIAddr during a renew.

=item

Added IP address decode for option 6 for the -p flag.

=back

=head3 1.0.4 09-24-2003

=over

=item

Revised the networking items for the Split Scope DHCP model. The 
program will send DHCP messages to both servers, but will only 
respond to the messages sent by the Primary DHCP server.

=back

=head3 1.0.3 09-23-2003 

=over

=item

Clean up of extraneous comments.

=item

Revised logic for sending and receiving Failover packets.

=back

=head3 1.0.2 09-12-2003

=over

=item

Removed references to the variable $lsock.

=item

Changed the default value of the Clusters to 25.

=item

Cleaned up nonfunctioning items from the option flags list screen.

=item

Removed MAC address verification that existed in a personal module.

=back

=head3 1.0.1 09-11-2003 

=over

=item

Muhammad helped me to optimize the networks sockets.

=back

=head3 1.0.0 09-11-2003 

=over

=item 

Option 61 is no longer exclusively tied to the client MAC address.  I 
added the global var $phone.  $phone accepts the user provided data 
using the -P option and the last four digits of the MAC addr.

=item 

The old -P option was rolled into screen debug level 1, which is the 
default screen logging option.

=back


       if ($match) { 
                last; 
              } else {
                pop(@without);
              }
            }
          }
          #### AKA Fussy Client.
          if ((!@with)&&(!@without)){
            my $reqAddr=$dhcppacket[2];
            $dhcppacket[2]=INADDR_ANY;
            $dhcppacket[6]="DHCP REQUEST";
            $dhcppacket[8]=&option_packer(50, $reqAddr).&option_packer(54,$dhcppacket[7]).$clientOptions{$dhcppacket[5]};
            push(@actionItems, @dhcppacket);
          } else {
            print PROGRESS chr(8)."x";
          }
          $i--;
          $offcount++;
        } else {
          print DEBUGTWO " for $dhcppacket[5]\n\tMAC address not found, or duplicate packet.\n\t\tDiscarding...\n";
          print PROGRESS chr(8)."I";
	  $ignoredPacketCounter++;
        } 
      } elsif ($dhcppacket[7] eq $splitserver){
        print DEBUGTWO "\n\tOFFER from the split scope server.\tIgnoring...\n";
        print PROGRESS chr(8)."I";
	$ignoredPacketCounter++;
      } else {
        print DEBUGTWO ", which is not under test.\n";
        print PROGRESS chr(8)."I";
	$ignoredPacketCounter++;
      }
    ###### Deal with ACKS ######
    } elsif ($dhcppacket[6] eq "DHCP ACK"){
      $j=0;
      if (($dhcppacket[7] eq $server)||
          ($dhcppacket[7] eq $foserver)||
          ($dhcppacket[7] eq $dualserver)||
          ($local==68)) {
        my $l=5;
        my $n=scalar(@temparray);
        while ($l <= $n){
	  #  It makes sense to accept both Offers and Requests as inputs for ACKS.
	  #    Since it is possible to code rapid commit in the input file as well
	  #    as on the command line.
          if (($dhcppacket[5] eq $temparray[$l])&&($temparray[$l+1] eq "DHCP REQUEST"||"DHCP OFFER")){
	    # The above line test for a MAC address that was sent and whether this
	    #   ACK is in response to a REQUEST or OFFER (Rapid Commit)
            splice(@temparray,($l-5), 9);
            last;
          } else {
            $l+=9;
          }
        } 
        if ($n>$l){
          my $oldAddr=$dhcppacket[2];
          if ($decodeOptionsServerPacket && $screenLogging >= 2){
            print DEBUGTWO "\n";
	    print DEBUGTWO "\tciAddr: $dhcppacket[1]\n";
	    print DEBUGTWO "\tyiAddr: $dhcppacket[2]\n";
	    print DEBUGTWO "\tsiAddr: $dhcppacket[3]\n";
	    print DEBUGTWO "\tgiAddr: $dhcppacket[4]\n";
	    print DEBUGTWO "\tchAddr: $dhcppacket[5]\n";
            &decodeOptions($dhcppacket[8]); 
          }
          ## Done Displaying ACK
          if ($dhcppacket[0] =~ /^\D\D\D\D/){
            ## Only xids that start with letter are post-processed. 
            my $test;
            if ($dhcppacket[0] =~ /^dddd/){
            ### Send DECLINE packet ###
              $test=$dhcppacket[0];
              $dhcppacket[0]=int(rand(99999999));
              $oldAddr=$dhcppacket[2];
              $dhcppacket[1]=$oldAddr;
              for (my $m=2; $m <= 4; $m++){
                $dhcppacket[$m]=INADDR_ANY;
              } 
              $dhcppacket[6]="DHCP DECLINE";
              $dhcppacket[8]="";
              push(@actionItems, @dhcppacket);
              ## ReDISCOVER after DECLINE
              if ($test !~ /^dddd..00/){
                my $count = substr($test,6,2);
                $count--;
                if ($count > 0){
		  $dhcppacket[0]="dddddd". sprintf("%2d",$count); # &dec2hex($count);
                } else { 
                  if ($inform) {
                    $dhcppacket[0]="cccc".sprintf("%2d", int(rand(99))).sprintf("%2d",$inform);
                  } elsif ($renew){
                    $dhcppacket[0]="bbbb".$renew.int(rand(9)).sprintf("%02d", $renewN);
                  } elsif ($release){
                    $dhcppacket[0]="eeee".$release.int(rand(9)).sprintf("%02d", $releaseN);
	          }
                }
                for (my $m=1; $m <= 3; $m++){
                  $dhcppacket[$m]=INADDR_ANY;
                } 
                $dhcppacket[4]=$giaddr;
                $dhcppacket[6]="DHCP DISCOVER";
                $dhcppacket[8]=&option_packer( 50, $oldAddr).$clientOptions{$dhcppacket[5]};
                unshift(@agenda, @dhcppacket);
              }
            ## end of DECLINE post processing
            } elsif ($dhcppacket[0] =~ /^cccc/){
            ### start of INFORM processing ###
              my $h=substr($dhcppacket[0],6,2);
	      my $tempciaddr=$dhcppacket[2];
              while ($h>0) {
                $dhcppacket[0]="ffffff".sprintf("%02d",$h);
		$dhcppacket[1]=$tempciaddr;
                $dhcppacket[2]=INADDR_ANY; 
                $dhcppacket[4]=$giaddr;
                $dhcppacket[6]="DHCP INFORM";
                $dhcppacket[8]=&option_packer( 43, "5e00");
                unshift(@agenda, @dhcppacket);
                $h--;
              }
              if ($renew){
                $dhcppacket[0]="bbbb".$renew.int(rand(9)).sprintf("%02d", $renewN);
                for (my $m=1; $m <= 3; $m++){
                  $dhcppacket[$m]=INADDR_ANY;
                } 
                $dhcppacket[4]=$giaddr;
                $dhcppacket[6]="DHCP DISCOVER";
                $dhcppacket[8]=&option_packer( 50, $oldAddr).$clientOptions{$dhcppacket[5]};
                unshift(@agenda, @dhcppacket);
              } elsif ($release){
                $dhcppacket[0]="eeee".$release.int(rand(9)).sprintf("%02d", $releaseN);
                for (my $m=1; $m <= 3; $m++){
                  $dhcppacket[$m]=INADDR_ANY;
                } 
                $dhcppacket[4]=$giaddr;
                $dhcppacket[6]="DHCP DISCOVER";
                $dhcppacket[8]=&option_packer( 50, $oldAddr).$clientOptions{$dhcppacket[5]};
                unshift(@agenda, @dhcppacket);
              }
            } elsif ($dhcppacket[0] =~ /^bbbb/){
            ### Start Renew post processing ###
              if ($dhcppacket[0] !~ /^bbbb..00/){ 
                my $count = substr($dhcppacket[0],6,2);               
                if ($count > 0){
                  $count--;
                  $dhcppacket[0]=substr($dhcppacket[0],0,6).sprintf("%02d", $count);
                  $dhcppacket[1]=$dhcppacket[2];
                  for (my $m=2; $m <= 3; $m++){
                     $dhcppacket[$m]=INADDR_ANY;
                  } 
		  	$dhcppacket[4]=$giaddr;
                  $dhcppacket[6]="DHCP REQUEST";
		  if ($opt82){
                    $dhcppacket[8]=substr($clientOptions{$dhcppacket[5]}, 0, -$o82len);
	          }else{
		    $dhcppacket[8]=$clientOptions{$dhcppacket[5]};
	          }
                }
                if ($dhcppacket[0] =~ /^....1/){
			if ($renewGiaddr){
				unshift(@agenda, @dhcppacket);
			} else {
				$dhcppacket[4]=INADDR_ANY;
				$dhcppacket[0]="ffffff00";
				for (my $p=1; $p<=$renewN; $p++){
					unshift(@agenda, @dhcppacket);
				} 
			}
                } else {
											       
			$dhcppacket[8].="030401020304";
			if ($renewGiaddr){
				push(@agenda, @dhcppacket);
			} else {
				$dhcppacket[4]=INADDR_ANY;
				$dhcppacket[0]="ffffff00";
				for (my $p=1; $p<=$renewN; $p++){
					push(@agenda, @dhcppacket);
				}
			}
                }                  
              } else {
                if ($release){
                  $dhcppacket[0]="eeee".$release.int(rand(9)).sprintf("%02d", $releaseN);
                  for (my $m=1; $m <= 3; $m++){
                    $dhcppacket[$m]=INADDR_ANY;
                  } 
                  $dhcppacket[4]=$giaddr;
                  $dhcppacket[6]="DHCP DISCOVER";
                  $dhcppacket[8]=&option_packer( 50, $oldAddr).$clientOptions{$dhcppacket[5]};
                  unshift(@agenda, @dhcppacket);
                }
              }
            ### End Renew post processing ###
            } elsif ($dhcppacket[0] =~ /^eeee/){
            ### Start RELEASE post processing ###
              my $test=$dhcppacket[0];
              $dhcppacket[0]="ffff".int(rand(9999));
              $dhcppacket[1]=$dhcppacket[2];
              for (my $m=2; $m <= 4; $m++){
                $dhcppacket[$m]=INADDR_ANY;
              } 
              $dhcppacket[6]="DHCP RELEASE";
              $dhcppacket[8]="";
              my $count=substr($test,6,2);
              $count--;
          