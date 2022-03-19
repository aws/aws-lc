#!/usr/bin/env perl

my $quiet = 1;

unpack("L",pack("N",1))!=1 || die "only little-endian hosts are supported";

# first argument can specify custom suffix...
$suffix=(@ARGV[0]=~/^\$/) ? shift(@ARGV) : "\$m";
#################################################################
# rename segments in COFF modules according to %map table below	#
%map=(	".text" => "fipstx$suffix",				#
	".text\$"=> "fipstx$suffix",				#
	".text\$mn"=> "fipstx$suffix",				#
	".rdata"=> "fipsrd$suffix",				#
	".data" => "fipsda$suffix"	);			#
#################################################################

print "suffix:[$suffix]\n" unless $quiet;
# collect file list
foreach (@ARGV) {
    if (/\*/)	{ push(@files,glob($_)); }
    else	{ push(@files,$_);       }
}

use Fcntl;
use Fcntl ":seek";

foreach (@files) {
    $file=$_;
    print "processing file $file\n" unless $quiet;

    sysopen(FD,$file,O_RDWR|O_BINARY) || die "sysopen($file): $!";

    # read IMAGE_DOS_HEADER
    sysread(FD,$mz,64)==64 || die "$file is too short";
    print "starting header\n" unless $quiet;
    @dos_header=unpack("a2C58I",$mz);
    $temp_header=@dos_header[0];
    print "header is $temp_header\n" unless $quiet;
    if ($temp_header eq "MZ") {
        print "file is a MZ\n" unless $quiet;
        $e_lfanew=pop(@dos_header);
        sysseek(FD,$e_lfanew,SEEK_SET)	|| die "$file is too short";
        sysread(FD,$Magic,4)==4		|| die "$file is too short";
        unpack("I",$Magic)==0x4550	|| die "$file is not COFF image";
    } elsif ($file =~ /\.obj$/i) {
        print "file is an object seeking\n" unless $quiet;
        # .obj files have no IMAGE_DOS_HEADER
        sysseek(FD,0,SEEK_SET)		|| die "unable to rewind $file";
    } else {
        print "skipping file\n" unless $quiet;
        next;
    }
    print "done header\n" unless $quiet;

    # read IMAGE_FILE_HEADER
    sysread(FD,$coff,20)==20 || die "$file is too short";
    ($Machine,$NumberOfSections,$TimeDateStamp,
     $PointerToSymbolTable,$NumberOfSysmbols,
     $SizeOfOptionalHeader,$Characteristics)=unpack("SSIIISS",$coff);

    # skip over IMAGE_OPTIONAL_HEADER
    sysseek(FD,$SizeOfOptionalHeader,SEEK_CUR) || die "$file is too short";

    print "Number of sections: $NumberOfSections\n" unless $quiet;
    # traverse IMAGE_SECTION_HEADER table
    for($i=0;$i<$NumberOfSections;$i++) {
        sysread(FD,$SectionHeader,40)==40 || die "$file is too short";
        ($Name,@opaque)=unpack("Z8C*",$SectionHeader);
        print "Section [$Name]\n" unless $quiet;
        if ($map{$Name}) {
            sysseek(FD,-40,SEEK_CUR) || die "unable to rewind $file";
            syswrite(FD,pack("a8C*",$map{$Name},@opaque))==40 || die "syswrite failed: $!";
            printf "    %-8s -> %.8s\n",$Name,$map{$Name} unless $quiet;
        }
    }
    close(FD);
}
