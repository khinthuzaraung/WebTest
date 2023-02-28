#!/usr/bin/perl
#################################################################################
#
#  Copyright 2022 Nokia Solutions and Networks Japan Corp. All Rights Reserved.
#  This product is protected by copyright and distributed.
#  under licenses restricting copying, modifying and distribution.
#
#  File Name
#  =====
#  SharePointUpload.pl
#
#  Description
#  =====
#  NetAct→SharePointへの自動転送ツール作成
#
#  Input
#  =====
#  無し
#
#  Output
#  =====
#　無し

#  Return
#  =====
#　無し

#  Additional Information
#  =====
#
#  History
#  =====
#  Ver1.0
#    2022/09/28 Khin ThuZar  Initial
#
#################################################################################
use strict;
use warnings;
# プラグマ
use FindBin;
use lib $FindBin::Bin.'/kpe_dbm/perllib';
use Cwd;
use Net::Telnet;
use Net::FTP;
use Com::Ftp;
use Com::Telnet;
use Com::Tool;
use Error qw(:try);
use DataTransferError;
use FTP421Error;
use LoginFailError;
use SystemError;
use File::Basename;
use Encode;
use Time::Local;
use kegis_attest_com;

my $TOOLDIR = $FindBin::Bin;
chdir $TOOLDIR;

my $LISTDIR = "$TOOLDIR/list";

# 接続先情報
# kcomserver02
my $LOCALNAME = "localhost";

# 日付取得
my $YYYYMMDD = &get_date(0,"yyyymmdd");
my $DATETIME = &get_date(0,"yyyymmdd_hhmmss");

my $TIMEOUTNUM = "60"; 
my $LOGDIR = "$TOOLDIR/Log/$YYYYMMDD";

# ログファイル
my $RESULTFILE = "${LOGDIR}/result_${DATETIME}.txt";
my $CONNECTLOG = "${LOGDIR}/connect_${DATETIME}.txt";

#mail宛先設定
my $TO = &read_list("$LISTDIR/mail_to.list");
my $FROM = &read_list("$LISTDIR/from.list"); 

# ディレクトリのチェック
if ( ! -d "$LOGDIR" )
{
    # 存在しない場合は作成する。
    system("mkdir -p $LOGDIR");
    system("chmod 775 $LOGDIR");
}

my $TOOL_CONF = "$TOOLDIR/conf/sharepoint_upload.conf";

#SharePointUpload 用 conf
#/work/SysPro/bin/conf/.Syspro_sharepoint_upload.conf
my $SHAREPOINT_INFO_CONF = "/work/SysPro/bin/conf/.Syspro_sharepoint_upload.conf";
#my $SHAREPOINT_INFO_CONF = "$TOOLDIR/conf/.Syspro_sharepoint_upload.conf";

my $KM_GLEM_CONF = "$TOOLDIR/conf/glem_server_list.conf";

my $USER  = "root"; # サーバのログインユーザ
my $PASS  = "NokiaSN123!"; # サーバのログインパスワード

my $UNIXGW_GRP = "NSN_NWI";

#my @UNIXGW_ID_LIST=`cat /project/db1/tool/kpe_dbm/unixgw_kegis/grp/${UNIXGW_GRP}/unixgw_manager.txt | grep UnixGW_ID | cut -d'=' -f2`;
my @UNIXGW_ID_LIST=`cat kpe_dbm/unixgw_kegis/grp/${UNIXGW_GRP}/unixgw_manager.txt | grep UnixGW_ID | cut -d'=' -f2`;
chomp($UNIXGW_ID_LIST[0]);
my $UNIXGW_ID = $UNIXGW_ID_LIST[0];

# UnixGW# 
#UnixGW管理者のアカウントを取得
#管理者のID_PASS定義ファイル
my $KEGISLIST = "/home/$UNIXGW_ID/.kegis";
#my $KEGISLIST = "/home/admin/.kegis";

# KIEF上のベースディレクトリを取得
#my @UNIXGW_ID_LIST=`cat /project/db1/tool/kpe_dbm/unixgw_kegis/grp/${UNIXGW_GRP}/unixgw_manager.txt | grep UnixGW_DIR | cut -d'=' -f2`;
@UNIXGW_ID_LIST=`cat kpe_dbm/unixgw_kegis/grp/${UNIXGW_GRP}/unixgw_manager.txt | grep UnixGW_DIR | cut -d'=' -f2`;
chomp($UNIXGW_ID_LIST[0]);


# cron01 ssh接続
my $PROMPT  = '/\$ $|> $/'; # [xxxxx]"$" command line / xxx">" command line

# sftp接続
my $ftpprompt='/sftp\> $/';

# ssh NETACT 接続
my $NETPROMPT  = '/# $/';

# ID_PASS情報のハッシュ可能
my %HASH_KEGIS = ();

# ハッシュキー情報を定義
my @HASH_KEY = ("UnixGW_HOST","UnixGW_ID","UnixGW_PASS","LOCAL_ID","LOCAL_PASS");

# KCOM 一時ディレクトリ
#Upload file directory /work/SharePoint_Upload_Tool/UploadData/$YYYYMMDD/$arg
#my $KCOMBASEDIR = "/var/tmp/$UNIXGW_ID_LIST[0]/toolwork/SharePoint_Upload_Tool/$YYYYMMDD";
my $KCOMBASEDIR = "/work/SharePoint_Upload_Tool/UploadData/$YYYYMMDD";

my $KCOMUPLOADDIR="/work/SharePoint_Upload_Tool/UploadData";

# CRON01 一時ディレクトリ
my $CRONBASEDIR = "/var/tmp/$UNIXGW_ID_LIST[0]/SharePoint_Upload_Tool";

#/d/oss/global/KDDI
my $NETACTDIR = "/d/oss/global/KDDI";
#my $NETACTDIR = "/var/tmp/sharepoint_upload_test/kddi";

my %FILE_HASH=();
my $TELNET;
my $FTP;
my $CRONTMPDIR;
my $SHARE_USERMAIL;
my $SHARE_MAILPW;
my $SHARE_UPLOADDIR;
my $SHARE_ADDRESS;
my $NETACT_SERVER;

#TOOL_CONF ファイルのチェック
if (! -f $TOOL_CONF) 
{
    print "No Such File: $TOOL_CONF\n";
    exit;
}

# tool.confファイルの読み込み処理
my %hash_toolconf = ();

my $conf_ans = &get_tool_conf($TOOL_CONF,\%hash_toolconf);

my $GLEM51IP  = $hash_toolconf{'KM-GLEM51'};
my $GLEM52IP  = $hash_toolconf{'KM-GLEM52'};
my $GLEM53IP  = $hash_toolconf{'KM-GLEM53'};
my $GLEM54IP  = $hash_toolconf{'KM-GLEM54'};
    
#SHAREPOINT_INFO_CONF ファイルのチェック
if (! -f $SHAREPOINT_INFO_CONF) 
{
    print "No Such File: $SHAREPOINT_INFO_CONF\n";
    exit;
}

# SHAREPOINT_INFO_CONFファイルの読み込み処理
my %hash_sharepointinfoconf = ();
my $conf_upload = &get_tool_conf($SHAREPOINT_INFO_CONF,\%hash_sharepointinfoconf);

# Sharenet Setting
$SHARE_USERMAIL = $hash_sharepointinfoconf{'SHAREPOINT_USER'};
$SHARE_MAILPW = $hash_sharepointinfoconf{'SHAREPOINT_PASS'};
$SHARE_UPLOADDIR= $hash_sharepointinfoconf{'UPLOAD_DIR'};
$SHARE_ADDRESS = $hash_sharepointinfoconf{'SHAREPOINT_ADDRESS'};


my @aryusr = split(/"/,$SHARE_USERMAIL);
foreach my $line (@aryusr)
{
	next if ($line eq "");
	$SHARE_USERMAIL = $line;
}

my @arypw = split(/"/,$SHARE_MAILPW);
foreach my $line (@arypw)
{
	next if ($line eq "");
	$SHARE_MAILPW = $line;
}
my @aryupdir = split(/"/,$SHARE_UPLOADDIR);
foreach my $line (@aryupdir)
{
	next if ($line eq "");
	$SHARE_UPLOADDIR = $line;
}

my @aryadd = split(/"/,$SHARE_ADDRESS);
foreach my $line (@aryadd)
{
	next if ($line eq "");
	$SHARE_ADDRESS = $line;
}

#KM_GLEM_CONF ファイルのチェック
if (! -f $KM_GLEM_CONF) 
{
    print "No Such File: $KM_GLEM_CONF\n";
    exit;
}

# SHAREPOINT_INFO_CONFファイルの読み込み処理
my %hash_kmglemconf = ();
my $conf_kmglem = &get_tool_conf($KM_GLEM_CONF,\%hash_kmglemconf);

my @GLEM_SERVER = ();

push(@GLEM_SERVER,$hash_kmglemconf{'KM-GLEM51'});
push(@GLEM_SERVER,$hash_kmglemconf{'KM-GLEM52'});
push(@GLEM_SERVER,$hash_kmglemconf{'KM-GLEM53'});
push(@GLEM_SERVER,$hash_kmglemconf{'KM-GLEM54'});

############
# 初期処理
############
# 認証情報ファイル
if ( ! -f $KEGISLIST )
{
    # エラー出力して、処理終了
    print "Not exist KEGIS Info file\n";
    exit 3;
}
else
{
    # 認証情報ファイルをオープンして情報を取得する。
    if ( ! open(KEGIS, $KEGISLIST) )
    {
        # エラー出力して、処理終了
        print "Can not open $KEGISLIST\n";
        exit 3;
    }

    #認証情報ファイルから下記のデータを取得する。
    #UnixGW_HOST=XXXXX
    #UnixGW_ID=XXXX
    #UnixGW_PASS=XXXXX
    #LOCAL_ID=XXXX
    #LOCAL_PASS=XXXXX
    while( my $line =<KEGIS> )
    {
        chomp($line);
        my @ary = split(/=/, $line);
        $HASH_KEGIS{$ary[0]} = $ary[1];
    }
    close(KEGIS);

    # 必要な情報が全て取得できているか確認する
    my $chk_key = "0";
    foreach my $key ( @HASH_KEY )
    {
        if ( defined $HASH_KEGIS{$key} )
        {
            if ( "$HASH_KEGIS{$key}" eq "" )
            {
                $chk_key = "1";
            }
        }
        else
        {
             # 必要な情報が取得できていない為、エラー終了
             $chk_key = "1";
        }
    }
    if ( $chk_key == 1 )
    {
        print "Error $KEGISLIST\n";
        exit 3;
    }
}

open(TMPFILE,">$RESULTFILE");
open(CONNECT,">$CONNECTLOG");

&remove_log();
&remove_kcom_temporary_directory();

foreach my $line (@GLEM_SERVER)
{
  &main($line); 
}

close(TMPFILE);
close(CONNECT);

################################################################################
# 関数名：main                                                                 #
# 概要  ：メイン処理。                                                         #
# 引数  ：GLEM SERVER NAME                                                                 #
# 戻り値：0：正常                                                              #
#         1：異常                                                              #
# グローバルへの書き込み：無し                                                 #
# 作成日:2022/09/28                                                             #
################################################################################
sub main($)
{
	my $arg = shift();
    my @disp = ();
    my @disp_split = ();
    my $linedata;
    my $ans = "";
    my $chk = "0";
    %FILE_HASH = ();

	# cron01一時ディレクトリ
	$CRONTMPDIR = "$CRONBASEDIR/$arg";
	#my $CRONTMPDIR = "/var/tmpwork/$UNIXGW_ID_LIST[0]/toolwork/SharePoint_Upload_Tool/$arg";

	if($arg eq "GLEM51")
	{
        $NETACT_SERVER = $GLEM51IP;
    }
    elsif($arg eq "GLEM52")
    {
    	$NETACT_SERVER = $GLEM52IP;
    }
    elsif($arg eq "GLEM53")
    {
    	$NETACT_SERVER = $GLEM53IP;
    }
    elsif($arg eq "GLEM54")
    {
    	$NETACT_SERVER = $GLEM54IP;
    }

    print TMPFILE "SERVER_NAME:$arg\n";
    print TMPFILE "NETACT_SERVER:$NETACT_SERVER\n";
    print "SERVER_NAME:$arg\n";
    print "NETACT_SERVER:$NETACT_SERVER\n";

    # KCOM TELNET CONNECT
    # ローカルホストにxxxユーザで本ツールを実行するため再ログイン
    $ans = &telnet_local($LOCALNAME,$HASH_KEGIS{'LOCAL_ID'},$HASH_KEGIS{'LOCAL_PASS'},\$TELNET,$TIMEOUTNUM,$PROMPT);
    if ( $ans != 0 )
    {
        return 1;
    }
    
    #cd $CRONTMPDIR
    $TELNET->print("cd $KCOMBASEDIR");
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    @disp_split = &ary_split(\@disp);
    foreach my $line (@disp_split)
    {
        if ( $line =~ /No\ssuch\sfile\sor\sdirectory/ )
        {           
            # 存在しない
            $TELNET->print("mkdir -p $KCOMBASEDIR");
   			@disp = $TELNET->waitfor($PROMPT);
    		print TMPFILE "@disp\n";
    		print @disp;

    		$TELNET->print("chmod 775 $KCOMBASEDIR");
   			@disp = $TELNET->waitfor($PROMPT);
    		print TMPFILE "@disp\n";
    		print @disp;

        }
    }
   
    # Cron01へログイン
    $ans = &ssh_unixgw($HASH_KEGIS{'UnixGW_HOST'},$HASH_KEGIS{'UnixGW_ID'},$HASH_KEGIS{'UnixGW_PASS'},\$TELNET,$PROMPT);
    
    if ( $ans != 0 )
    {
        return 1;
    }

 	  # ログ出力
      &logcloseopen();


    $TELNET->print("rm -rf $CRONTMPDIR");
   	@disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;
            
    # 存在しない
    $TELNET->print("mkdir -p $CRONTMPDIR");
   	@disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    $TELNET->print("chmod 775 $CRONTMPDIR");
   	@disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;   		

	#ログ出力
	&logcloseopen();
 
    #NetACT FTP CONNECT
    &connectlogtimer("FTP",$NETACT_SERVER,"LOGIN START");
 
    $ans = &activelan_sftp_connect($NETACT_SERVER,$USER,$PASS,\$TELNET,$ftpprompt,\@disp);
    if ( $ans != 0 )
    {
        # TELNET DISCONNECT
        $TELNET->print("exit");
        $TELNET->close;
        &connectlogtimer("FTP",$NETACT_SERVER,"LOGIN NG");
        return 1;
    }

    &connectlogtimer("FTP",$NETACT_SERVER,"LOGIN OK");

    #ログ出力
    &logcloseopen();

    $ans = &ch_directory_check($arg);
    
    # netact sftp
    $TELNET->print("exit");

    if ( $ans == 0 )
    {
        &make_ch_directory();

    	&get_ch_directory($arg);

     	&ftp_get($arg);

     	my $result = &sharepoint_upload($arg);
     	if ($result == 1) 
     	{
     		return $result; 
     	}
        else
        {
            my $mailresult = &normal_mail($arg,\%FILE_HASH);        
            if ($mailresult == 1) 
            {
                return $mailresult; 
            }

            &uploadfolder_delete($arg,\%FILE_HASH);
        }


    }

}


################################################################################
# 関数名：ch_directory_check                                                    #
# 概要  ："CH-"で始まるディレクトリが存在確認                                          #
# 引数  ：無し                                                                   #
# 戻り値：                                                                       #
# 作成日:2022/09/28                                                           #
################################################################################
sub ch_directory_check($)
{
	my $glem = shift;
    my $flag = "2";
    my @disp = ();
    my @disp_split = ();
    my $chk = "0";
    my $cnt = "0";
    my $chflg = "0";
    my $notchflg = "0";   

    eval
    {
        # ログ出力
        &logcloseopen();

        # CH ls
        #$TELNET->print("cd /d/oss/global/KDDI");
        $TELNET->print("cd $NETACTDIR");
        @disp = $TELNET->waitfor($ftpprompt);
        print TMPFILE "@disp\n";
        print @disp;

        my @dircheck = &ary_split(\@disp);
    	foreach my $line (@dircheck)
    	{
       	 	if ( $line =~ /No\ssuch\sfile\sor\sdirectory/ )
        	{ 
        		print TMPFILE "NETACTDIR[$glem]:No such file or directory.\n";
        		return 1;
        	}
    	}

        $TELNET->print("ls -l ");
        @disp = $TELNET->waitfor($ftpprompt);
        print TMPFILE "@disp\n";
        print @disp;
       
        my %DIRLIST_HASH = ();
   		
   		@disp_split = &ary_split(\@disp);

   		#書き込み中のファイル確認START
		foreach my $line (@disp_split) 
		{
			my $tmp_time="";
			my $tmp_dirname="";
			$line =~ s/\x0D\x0A|\x0D|\x0A/\n/g;
     		chomp($line);
    		next if($line eq "");

    		if ( $line =~ /^.*\s+(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)\s+\d+\s+([0-9:]+)\s+(.+)$/ )
    		{
    			$tmp_time = $2;
        		$tmp_dirname = $3;
    			#print "Time:|$2|FileName:|$3|\n";
    			if ( $tmp_dirname =~ /^CH-/)
    			{
        			$DIRLIST_HASH{"$tmp_dirname"} = $tmp_time;
    			}
    		}    			
		} 
		 
		print TMPFILE "INFO:60s sleep\n";
        print "INFO:60s sleep\n";

        sleep 60;

        $TELNET->print("ls -l");
        @disp = $TELNET->waitfor($ftpprompt);
        print TMPFILE "@disp\n";
        print @disp;
       
       	@disp_split = &ary_split(\@disp);
        foreach my $line (@disp_split) 
		{

			my $tmp_comptime="";
			my $tmp_compdirname="";
			$line =~ s/\x0D\x0A|\x0D|\x0A/\n/g;
    		chomp($line);
    		next if($line eq "");

    		if ( $line =~ /^.*\s+(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)\s+\d+\s+([0-9:]+)\s+(.+)$/ )
    		{
    			#print "Time:|$2|FileName:|$3|\n";
    			$tmp_comptime = $2;
        		$tmp_compdirname = $3;
        		# CH-からはじまるdirectoryかCheck
        		if ( $tmp_compdirname =~ /^CH-/)
    			{
    				$chflg=1;

        			if ( exists($DIRLIST_HASH{"$tmp_compdirname"}))
			 		{
			 			# 書き込み中ではないCH-ディレクトリの場合、HASHに格納する
        				if ( $DIRLIST_HASH{"$tmp_compdirname"} eq $tmp_comptime )
			 			{
			 				$FILE_HASH{"$tmp_compdirname"} = "$tmp_compdirname";
			 				#書き込む中ファイルじゃないのファイルのchk
			 				$chk = 1;
			 				$flag = 0;
			 			}
			   	 	}    				
    			}
    			else
    			{
    				$notchflg=1;
    				$cnt++;
    			}
        
    		}   
		}
		#書き込み中のファイル確認END

		#CH-からはじまるファイルかつCH以外のファイルがある場合
  		if($chflg == 1 && $notchflg == 1)
  		{
  			&warning_mail($glem,$cnt,\@disp_split);
  			&connectlogtimer("FTP",$NETACT_SERVER,"Other files exist.");
  		}

        if ( $chk == 0 )
        {
            &connectlogtimer("FTP",$NETACT_SERVER,"No Such File:start with 'CH-'.");
            $flag = 1;
            #return;
        }

        # ログ出力
        &logcloseopen();
    };

    if($@)
    {
        &connectlogtimer("FTP",$NETACT_SERVER,"FTP Session Disconnect?");
        $flag = "3";
    }

    # ログ出力
    &logcloseopen();

    return $flag;
}

################################################################################
# 関数名：make_ch_directory                                                    #
# 概要  ："CH-"で始まるディレクトリ作成                                          #
# 引数  ：無し                                                                   #
# 戻り値：                                                                       #
# 作成日:2022/12/01                                                          #
################################################################################
sub make_ch_directory()
{
    my @disp = ();

    foreach my $directory (keys(%FILE_HASH))
    {
        $TELNET->print("cd $CRONTMPDIR");
        @disp = $TELNET->waitfor($PROMPT);
        print TMPFILE "@disp\n";
        print @disp;

        # 存在しない
        $TELNET->print("mkdir $directory");
        @disp = $TELNET->waitfor($PROMPT);
        print TMPFILE "@disp\n";
        print @disp;

        $TELNET->print("chmod 775 $directory");
        @disp = $TELNET->waitfor($PROMPT);
        print TMPFILE "@disp\n";
        print @disp; 
    }     
}

################################################################################
# 関数名：get_ch_directory                                                   #
# 概要  ："CH" で始まるディレクトリを取得してcronサーバの一時ディレクトリに格納する                                       #
# 引数  ：無し                                                                   #
# 戻り値：                                                                       #
# 作成日:2022/09/28                                                            #
################################################################################
sub get_ch_directory($)
{
    my $glem = shift;
    my $flag = "0";
    my @disp = ();
    my @disp_split = ();
    my $chk = 0;
    my @print = ();
    my $ans = "";

    #NetACT FTP CONNECT
    &connectlogtimer("FTP",$NETACT_SERVER,"LOGIN START");
 
    $ans = &activelan_sftp_connect($NETACT_SERVER,$USER,$PASS,\$TELNET,$ftpprompt,\@disp);
    if ( $ans != 0 )
    {
        # TELNET DISCONNECT
        $TELNET->print("exit");
        $TELNET->close;
        &connectlogtimer("FTP",$NETACT_SERVER,"LOGIN NG");
        return 1;
    }

    &connectlogtimer("FTP",$NETACT_SERVER,"LOGIN OK");

    eval
    {
        # ログ出力
        &logcloseopen();


        foreach my $directory (keys(%FILE_HASH))
        {
            # lcd to cron01
            $TELNET->print("lcd $CRONTMPDIR/$directory");
            @disp = $TELNET->waitfor($ftpprompt);
            print TMPFILE "@disp\n";
            print @disp;

            # CH ls
            $TELNET->print("cd $NETACTDIR");
            @disp = $TELNET->waitfor($ftpprompt);
            print TMPFILE "@disp\n";
            print @disp;

            $TELNET->print("ls $directory");
            @disp = $TELNET->waitfor($ftpprompt);
            print TMPFILE "@disp\n";
            print @disp;

            my @file_split = &ary_split(\@disp);
            foreach my $file (@file_split) 
            {
               $file =~ s/\x0D\x0A|\x0D|\x0A/\n/g;
               chomp($file);

        	   $TELNET->print("get -r $file");
        	   @disp = $TELNET->waitfor($ftpprompt);
        	   print TMPFILE "@disp\n";
        	   print @disp;
            }

        	$chk = 1;
        }

        if ( $chk == 1 )
        {
            &connectlogtimer("FTP",$NETACT_SERVER,"FILE GET SUCCESS!");
        }

        if ( $chk == 0 )
        {
            &connectlogtimer("FTP",$NETACT_SERVER,"FILE GET FAILURE!");
        }

        if ( $chk == 1 )
        {
        	# netact sftp
        	$TELNET->print("exit");
        	# cron01 ssh
        	@disp = $TELNET->waitfor($PROMPT);
        	print TMPFILE "@disp\n";
        	print @disp;

        	$TELNET->print("cd $CRONTMPDIR/..");
   		    @disp = $TELNET->waitfor($PROMPT);
        	print TMPFILE "@disp\n";
        	print @disp;

    	    $TELNET->print("tar zcvf ${glem}.tgz $glem");
   		    @disp = $TELNET->waitfor($PROMPT);
        	print TMPFILE "@disp\n";
        	print @disp;
        }
        else
        {
        	$TELNET->print("exit");
        }

        #$TELNET->close;
        
        # ログ出力
        &logcloseopen();
    };

    if($@)
    {
        &connectlogtimer("FTP",$NETACT_SERVER,"FTP Session Disconnect?");
        $flag = "3";
    }

    return $flag;
}

################################################################################
# 関数名：ftp_get                                                   #
# 概要  ：cronから取得したデータをkcomサーバに移動                                       #
# 引数  ：無し                                                                   #
# 戻り値：                                                                       #
# 作成日:2022/09/28                                                            #
################################################################################
sub ftp_get($)
{
	my $glem = shift;
	my @disp = ();
    my @disp_split = ();	
    my $LOG_INFO = "INFO";
	my $con;
	my $ans;

	my $tool = Com::Tool->new();

    # ConnectLog出力用
    &connectlogtimer("FTP","CRON01","LOGIN START");

    #cron sftp 接続
	my $ftp_con = Com::Ftp->new($HASH_KEGIS{'UnixGW_HOST'},$HASH_KEGIS{'UnixGW_ID'},$HASH_KEGIS{'UnixGW_PASS'});
			
	my @ans=$ftp_con->connect();
    print TMPFILE "@ans\n";
    print @ans;

    @ans=$ftp_con->login();
    print TMPFILE "@ans\n";
    print @ans;

    @ans=$ftp_con->cwd("$CRONTMPDIR/..");
    print TMPFILE "@ans\n";
    print @ans;

    @ans=$ftp_con->bin();
    print TMPFILE "@ans\n";
    print @ans;

    @ans=$ftp_con->ls();
    print TMPFILE "@ans\n";
    print @ans;

    @disp_split = &ary_split(\@ans);
    foreach my $line (@disp_split)
    {
    	my $getfile = "${glem}.tgz";

    	print "GET TAR FILE:$line\n";

    	if($line eq $getfile)
    	{
    		$tool->cd("$KCOMBASEDIR");

    	 	@ans=$ftp_con->get($line);
    	 	print TMPFILE "@ans\n";
    	 	print @ans;
    	}

    	# 移動ログ
        &connectlogtimer("LOG_INFO","cron01 -> kcom02","FileTransfer Success.");
    }	

    # ログ出力
    &logcloseopen();

    @ans=$ftp_con->quit();
    print TMPFILE "@ans\n";
    print @ans;	

    $TELNET->print("exit");

    # ログ出力
    &logcloseopen();	
}

################################################################################
# 関数名：sharepoint_upload                                                   #
# 概要  ：sharepointアップロード処理                                          #
# 引数  ：無し                                                                   #
# 戻り値：                                                                       #
# 作成日:2022/09/28                                                             #
################################################################################
sub sharepoint_upload($)
{
	my $glem = shift;
    #my $flag = "2";
    my $flag = 1;
    my $chk = "1";
    my $chkcnt = 0;
	my @disp = ();
	my @disp_split = ();
	my @uploadfile = ();
	my $ans;
	my $lines;
	my %HASH_UPLOAD = ();

	# KIEF TELNET CONNECT
    # ローカルホストにxxxユーザで本ツールを実行するため再ログイン
    # $ans = &telnet_local($LOCALNAME,$HASH_KEGIS{'LOCAL_ID'},$HASH_KEGIS{'LOCAL_PASS'},\$TELNET,$TIMEOUTNUM,$PROMPT);
    # if ( $ans != 0 )
    # {
    #     return 1;
    # }

    # ログ出力
	&logcloseopen();    

    # cd $KCOMBASEDIR
    $TELNET->print("cd $KCOMBASEDIR");
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    $TELNET->print("tar zxvf ${glem}.tgz");
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    $TELNET->print("cd $glem");
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    @disp_split = &ary_split(\@disp);
    foreach my $line (@disp_split)
    {
         if ( $line =~ /No\ssuch\sfile\sor\sdirectory/ )
         {
         	return 1;
         }
    }

    $TELNET->print("ls -1");
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;
    # @disp = `ls -1`;
    # print TMPFILE "@disp\n";

    @disp_split = &ary_split(\@disp);

    foreach my $line ( @disp_split )
    {  
    	if($line =~ /^CH-/)
    	{
            $TELNET->print("find $line/* -ls");
            @disp = $TELNET->waitfor($PROMPT);
            print TMPFILE "@disp\n";
            print @disp;

            @disp_split = &ary_split(\@disp);
            foreach my $getfile (@disp_split)
            {
                #print "FIND :$getfile\n";
                
                if ( $getfile =~ /No\ssuch\sfile\sor\sdirectory/ )
                {
                    #何もしない
                }
                elsif($getfile =~ /^kcomserv02:/)
                 {
                    #何もしない
                 }
                elsif($getfile =~ /^>/)
                {
                    #何もしない
                }
                elsif($getfile =~ /^find\s/)
                {
                    #何もしない
                }
                else
                {
                    #$TELNET->print("php $TOOLDIR/php/SPOFileUtil.php 'https://nokia.sharepoint.com/sites/toolg' '$SHARE_USERMAIL' '$SHARE_MAILPW'  'C' '/sites/toolg/Shared Documents/uploadtest' '$line'");
                    $TELNET->print("php $TOOLDIR/php/SPOFileUtil.php 'https://nokia.sharepoint.com/sites/LTEwithMOC' '$SHARE_USERMAIL' '$SHARE_MAILPW'  'C' '/sites/LTEwithMOC/Shared Documents/Log置き場' '$line'");
                    @disp = $TELNET->waitfor($PROMPT);
                    print TMPFILE "@disp\n";
                    print @disp;

                    $TELNET->print("find $line/* -ls");
                    @disp = $TELNET->waitfor($PROMPT);
                    print TMPFILE "@disp\n";
                    print @disp;

                    @uploadfile = &ary_split(\@disp);
                    foreach my $uploaddir (@uploadfile)
                    {
                        my $var;

                        $uploaddir =~ s/\x0D\x0A|\x0D|\x0A/\n/g;
                        chomp($uploaddir);
                        next if($uploaddir eq "");
                        next if($uploaddir eq "find $line/* -ls");
                
                        if ( $uploaddir =~ /^([0-9]+)\s+([0-9]+)\s+(.+)\s+([0-9]+)\s+(.+)\s+(.+)\s+([0-9]+)\s+(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)\s+\d+\s+([0-9:]+)\s+(.+)$/ )
                        {
                            print "TYPE:|$3|FileName:|$10|\n";
                            my $Type = $3;
                            my $File = $10;
                            if($Type =~ /^d/)
                            {
                                print "DIR\n";
                                my @dircreate = &ary_splitslash($File);
                                foreach my $arydir (@dircreate)
                                {
                                    print "$arydir\n";
                            
                                    if(!defined($var))
                                    {
                                        $var = "$arydir";
                                        #$TELNET->print("php $TOOLDIR/php/SPOFileUtil.php 'https://nokia.sharepoint.com/sites/toolg' '$SHARE_USERMAIL' '$SHARE_MAILPW'  'C' '/sites/toolg/Shared Documents/uploadtest' '$var'");
                                        $TELNET->print("php $TOOLDIR/php/SPOFileUtil.php 'https://nokia.sharepoint.com/sites/LTEwithMOC' '$SHARE_USERMAIL' '$SHARE_MAILPW'  'C' '/sites/LTEwithMOC/Shared Documents/Log置き場' '$var'");
                                        @disp = $TELNET->waitfor($PROMPT);
                                        print TMPFILE "@disp\n";
                                        print @disp;
                                    }
                                    else
                                    {
                                        #print "php $TOOLDIR/php/SPOFileUtil.php 'https://nokia.sharepoint.com/sites/toolg' '$SHARE_USERMAIL' '$SHARE_MAILPW'  'C' '/sites/toolg/Shared Documents/uploadtest/$var/' '$arydir'";

                                        #$TELNET->print("php $TOOLDIR/php/SPOFileUtil.php 'https://nokia.sharepoint.com/sites/toolg' '$SHARE_USERMAIL' '$SHARE_MAILPW'  'C' '/sites/toolg/Shared Documents/uploadtest/$var/' '$arydir'");
                                        $TELNET->print("php $TOOLDIR/php/SPOFileUtil.php 'https://nokia.sharepoint.com/sites/LTEwithMOC' '$SHARE_USERMAIL' '$SHARE_MAILPW'  'C' '/sites/LTEwithMOC/Shared Documents/Log置き場/$var/' '$arydir'");
                                        @disp = $TELNET->waitfor($PROMPT);
                                        print TMPFILE "@disp\n";
                                        print @disp;

                                        $var .= "/$arydir";                             
                                    }
                                }
                                #print "path:$var\n";
                            }
                            elsif($Type =~ /^-/)
                            {
                                print "DEBUG:UPLOADFILE:$File\n";

                                my @dircreate = &ary_splitslash($File);
                                my $filepath;

                                for(my $i = 0; $i < $#dircreate; $i++)
                                {
                                    print("$dircreate[$i] \n");
                                    if(!defined($filepath))
                                    {
                                        $filepath .="$dircreate[$i]";
                                    }
                                    else
                                    {
                                        $filepath .="/$dircreate[$i]";
                                    }
                                }

                                #print "python $TOOLDIR/Office365-REST-Python-Client/upload_large_file.py https://nokia.sharepoint.com/sites/toolg $SHARE_USERMAIL $SHARE_MAILPW /sites/toolg/Shared Documents/uploadtest/$line $KCOMBASEDIR/$glem/$File\n";
                                #$TELNET->print("./$TOOLDIR/Office365-REST-Python-Client/upload_large_file https://nokia.sharepoint.com/sites/LTEwithMOC $SHARE_USERMAIL $SHARE_MAILPW '/sites/LTEwithMOC/Shared Documents/Log驗ゑｽｮ邵ｺ讎刈・ｴ/$filepath' $KCOMBASEDIR/$glem/$File");
                                #@disp = $TELNET->waitfor($PROMPT);
                                #print TMPFILE "@disp\n";
                                #print @disp; 
                                #system("pwd");
                                #$TELNET->print("cd  $TOOLDIR");
                                # @disp = $TELNET->waitfor($PROMPT);
                                # print TMPFILE "@disp\n";
                                # print @disp; 

                                # #print("./upload_large_file https://nokia.sharepoint.com/sites/LTEwithMOC $SHARE_USERMAIL $SHARE_MAILPW '/sites/LTEwithMOC/Shared Documents/Log驗ゑｽｮ邵ｺ讎刈・ｴ/$filepath' $KCOMBASEDIR/$glem/$File");
                                #$TELNET->print("./upload_large_file https://nokia.sharepoint.com/sites/LTEwithMOC $SHARE_USERMAIL $SHARE_MAILPW '/sites/LTEwithMOC/Shared Documents/Log驗ゑｽｮ邵ｺ讎刈・ｴ/$filepath' $KCOMBASEDIR/$glem/$File");
                                # @disp = $TELNET->waitfor($PROMPT);
                                # print TMPFILE "@disp\n";
                                # print @disp; 
                                #system("./upload_large_file https://nokia.sharepoint.com/sites/LTEwithMOC $SHARE_USERMAIL $SHARE_MAILPW '/sites/LTEwithMOC/Shared Documents/Log驗ゑｽｮ邵ｺ讎刈・ｴ/$filepath' $KCOMBASEDIR/$glem/$File");

                                my $path_base = '/sites/LTEwithMOC/Shared Documents/Log置き場';
                                #my $list=system("$TOOLDIR/upload_large_file https://nokia.sharepoint.com/sites/toolg $SHARE_USERMAIL $SHARE_MAILPW '$path_base/$filepath' $KCOMBASEDIR/$glem/$File");
                                my $list=system("$TOOLDIR/upload_large_file https://nokia.sharepoint.com/sites/LTEwithMOC $SHARE_USERMAIL $SHARE_MAILPW '$path_base/$filepath' $KCOMBASEDIR/$glem/$File");                                        
                                #my $list         ="success";               
                                print TMPFILE "$list\n";
                                print $list; 

                                if(!defined($list))
                                {
                                    $chk = 2;
                                    print TMPFILE "SHARE_POINT UPLOADED UNSUCCESSFUL.\n";
                                    print @disp;
                                }
                                else
                                {
                                    $chk = 1;
                                    print TMPFILE "SHARE_POINT UPLOADED SUCCESSFULLY.\n";
                                    print @disp;
                                    $chkcnt++;
                                }
                            }
                        }
                    }
                }
            }
    	}
    }

    if ( $chk == 1 && $chkcnt > 0)
    {
        if($chkcnt != 0)
        {
            $flag = 2;
        }
        else
        {
            $flag = 1;
        }
    }
    if ( $chk == 2 && $chkcnt == 0)
    {
        $flag = 1;
    }


    #ログ出力
	&logcloseopen();

    return $flag;	
}

################################################################################
# 関数名：sharepoint_upload                                                   #
# 概要  ：sharepointアップロードした後対象ファイル削除処理                                          #
# 引数  ：無し                                                                   #
# 戻り値：                                                                       #
# 作成日:2022/09/28                                                              #
################################################################################
sub uploadfolder_delete($)
{
	my $glem = shift;
    my $file_hash =shift;
	my @disp = ();
	my @disp_split = ();
	my $ans;
	
    foreach my $line (values %{$file_hash})
    {
    # NETACTのメインディレクトリへ移動する
        $TELNET->print("cd $NETACTDIR");
        @disp = $TELNET->waitfor($NETPROMPT);
        print TMPFILE "@disp\n";
        print @disp;
	
        print "DEBUG:DELETEDIR:$line\n";
        $TELNET->print(" rm -r $line/*");
        @disp = $TELNET->waitfor($NETPROMPT);
        print TMPFILE "@disp\n";
        print @disp;
    }

	# ログ出力
	&logcloseopen();

	$TELNET->print("find CH-* -type d -empty -mtime +7");#-mtime +7
    @disp = $TELNET->waitfor($NETPROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    @disp_split = &ary_split(\@disp);
    foreach my $line (@disp_split)
    {
    	print "DEBUG:EMPTYDIR:$line\n";
    	if ( $line !~ /^ls -l/ && $line !~ /^\[/ && $line !~ /^#/ && $line !~ /^find/)    
        {
        	$TELNET->print("rmdir $line");
    		@disp = $TELNET->waitfor($NETPROMPT);
    		print TMPFILE "@disp\n";
    		print @disp;
        }

    }   

    $TELNET->print("exit");

    # cron01 ssh
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    $TELNET->print("cd $CRONBASEDIR");
   	@disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    $TELNET->print("rm -rf $glem");
   	@disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    $TELNET->print("rm -rf ${glem}.tgz");
   	@disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    #$TELNET->close;
    $TELNET->print("exit");
	
    #rename uploaded file
    $TELNET->print("cd $KCOMBASEDIR");
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    $TELNET->print("cd $KCOMBASEDIR");
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

   #$TELNET->print("pwd");

    $TELNET->print("cp -r $glem ${glem}.${DATETIME}");
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    $TELNET->print("chmod 777 ${glem}.${DATETIME}");
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    $TELNET->print("rm -rf $glem");
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    $TELNET->print("cp -r ${glem}.tgz ${glem}.${DATETIME}.tgz");
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    system("rm ${glem}.tgz");

    $TELNET->close;
    # ログ出力
	&logcloseopen();

}


################################################################################
# 関数名：warning_mail                                                    #
# 概要  ："CH-"で始まるディレクトリが存在確認                                          #
# 引数  ：無し                                                                   #
# 戻り値：                                                                       #
# 作成日:2022/09/28                                                              #
################################################################################
sub warning_mail($)
{
	my $glem = shift;
	my $count = shift;
    my $ary = shift;
    my $mail_title_header = "";
    my $mail_data = "";
    my @disp = ();
    my @disp_split = ();

    $mail_title_header = "[WARNING] $glem : The other file is included.";
    
    eval
    {
    	$mail_data .= "$count file(s) found in $NETACTDIR on NetAct(KM-$glem).\n";

        foreach my $line ( @{$ary} )
    	{  
    		if($line !~ /^ls -l/ && $line !~ /^sftp>/)
    		{
    			if ($mail_data eq "")
    			{
    				$mail_data = "$line\n";
    			}
    			else
    			{
    				$mail_data .= "$line\n";
    			}
    		}

    	}
    	$mail_data .= "(kcomserv02):$TOOLDIR/SharePointUpload.pl\n";

    	system("$TOOLDIR/send_mail.pl $TO \"$mail_title_header\" $FROM \"$mail_data\"");

    	print TMPFILE "[WARNING]MAIL SEND SUCCESSFUL!\n";
    }   
}

################################################################################
# 関数名：normal_mail                                                    #
# 概要  ：sharepoint にファイルの転送があった時にはメール送信(NORMAL)                                         #
# 引数  ：無し                                                                   #
# 戻り値：                                                                       #
# 作成日:2022/09/28                                                            #
################################################################################
sub normal_mail($)
{
	my $glem = shift;
	my @uploadfile = ();
	my $file_hash =shift;
    my $mail_title_header = "";
    my $mail_data = "";
    my @disp = ();
    my @disp_split = ();
    my $ans;
    my $cnt = 0;


    # ログ出力
	&logcloseopen();

    # KCOM TELNET CONNECT
    # ローカルホストにxxxユーザで本ツールを実行するため再ログイン
    # $ans = &telnet_local($LOCALNAME,$HASH_KEGIS{'LOCAL_ID'},$HASH_KEGIS{'LOCAL_PASS'},\$TELNET,$TIMEOUTNUM,$PROMPT);
    # if ( $ans != 0 )
    # {
    #     return 1;
    # }
    
    # Cron01へログイン
    $ans = &ssh_unixgw($HASH_KEGIS{'UnixGW_HOST'},$HASH_KEGIS{'UnixGW_ID'},$HASH_KEGIS{'UnixGW_PASS'},\$TELNET,$PROMPT);
    
    if ( $ans != 0 )
    {
        return 1;
    }

    # NetACT SSH CONNECT
    &connectlogtimer("SSH",$NETACT_SERVER,"LOGIN START");
 
    $ans = &activelan_ssh_connect($NETACT_SERVER,$USER,$PASS,\$TELNET,$NETPROMPT,\@disp);

    if ( $ans != 0 )
    {
        # TELNET DISCONNECT
        $TELNET->print("exit");
        $TELNET->close;
        &connectlogtimer("SSH",$NETACT_SERVER,"LOGIN NG");
        return 1;
    }

    &connectlogtimer("SSH",$NETACT_SERVER,"LOGIN OK");
    
     eval
    {
        # CH ls
        #$TELNET->print("cd /d/oss/global/KDDI");
        $TELNET->print("cd $NETACTDIR");
        @disp = $TELNET->waitfor($NETPROMPT);
        print TMPFILE "@disp\n";

        foreach my $line (values %{$file_hash})
        {
            print "FILE_HASH:$line\n";
            $TELNET->print("ls -l $NETACTDIR/$line");
            @disp = $TELNET->waitfor($NETPROMPT);
            print TMPFILE "@disp\n";

            @uploadfile = &ary_split(\@disp);

            foreach my $file (@uploadfile)
            {
                if( $file !~ /^ls -l/ && $file !~ /^\[/ && $file !~ /^total/ && $file !~ /^#/)
                {
                    if ($mail_data eq "")
                    {
                        $mail_data = "$file\n";
                        $cnt++;
                    }
                    else
                    {
                        $mail_data .= "$file\n";
                        $cnt++;
                        
                    }
                }
            }

            $mail_title_header = "[NORMAL] $glem: $line File Transferred";
            $mail_data .= "$cnt file(s) found in $line on NetAct(KM-$glem).\n";
            $mail_data .= "$cnt file(s) transfer succeeded.\n";
            $mail_data .= "$cnt file(s) deleted.\n";
            $mail_data .= "(kcomserv02):$TOOLDIR/SharePointUpload.pl\n";
            if($cnt != 0)
            {
                system("$TOOLDIR/send_mail.pl $TO \"$mail_title_header\" $FROM \"$mail_data\"");
                print TMPFILE "[NORMAL] MAIL SEND SUCCESSFUL!\n"; 
            }

            $mail_data = "";
            $cnt = 0;
        }
    }  
}

###########################################################
# listからデータを取得する
# 戻り値
# 0:正常
# 1:ファイル無
# 2:ファイルオープンエラー
# 作成日:2022/09/28 
###########################################################
sub read_list($)
{
    my $list = shift;
    my $cnt = 0;
    my $ans = "";

    open(IN,"$list");
    while (my $line = <IN> )
    {
        chomp($line);
        if ( $cnt == 0 )
        {
            $ans = $line;
        }
        else
        {
            $ans .= "," . $line;
        }
        $cnt++;
    }
    close(IN);

    return  $ans;

}

################################################################################
# 関数名：remove_kcom_temporary_directory                                                    #
# 概要  ：2週間以上の一時ディレクトリの削除                                          #
# 引数  ：無し                                                                   #
# 戻り値：                                                                       #
# 作成日:2022/09/28                                                              #
################################################################################
sub remove_kcom_temporary_directory()
{
    my @disp = ();
    my @disp_split = ();

    # ログ出力
    &logcloseopen();

    # KCOM TELNET CONNECT
    # ローカルホストにxxxユーザで本ツールを実行するため再ログイン
    my $ans = &telnet_local($LOCALNAME,$HASH_KEGIS{'LOCAL_ID'},$HASH_KEGIS{'LOCAL_PASS'},\$TELNET,$TIMEOUTNUM,$PROMPT);
    if ( $ans != 0 )
    {
        return 1;
    }

    $TELNET->print("cd $KCOMUPLOADDIR");
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    my @dircheck = &ary_split(\@disp);
    foreach my $line (@dircheck)
    {
       	if ( $line =~ /No\ssuch\sfile\sor\sdirectory/ )
        { 
        	print TMPFILE "No such file or directory.\n";
        	return 1;
        }
    }

    $TELNET->print("find -type d -mtime +14");#-mtime +7
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    @disp_split = &ary_split(\@disp);
    foreach my $line (@disp_split)
    {
    	print "KCOMTEMPDIR:$line\n";
    	if($line =~ /^kcomserv02/ || $line =~ /^>/ || $line =~ /^\[/ || $line =~ /^find -type d -mtime \+14/ || $line =~ /^\$/)
    	{
    		#何もしない
    	}
    	else
    	{
    		$TELNET->print("rm -rf $line");#-mtime +7
    		@disp = $TELNET->waitfor($PROMPT);
    		print TMPFILE "@disp\n";
    		print @disp;
    	}
    } 

    $TELNET->close;  

}

################################################################################
# 関数名：remove_log                                                 #
# 概要  ：2週間以上のログファイルの削除                                          #
# 引数  ：無し                                                                   #
# 戻り値：                                                                       #
# 作成日:2022/09/28                                                            #
################################################################################
sub remove_log()
{
    my @disp = ();
    my @disp_split = ();

    # KCOM TELNET CONNECT
    # ローカルホストにxxxユーザで本ツールを実行するため再ログイン
    my $ans = &telnet_local($LOCALNAME,$HASH_KEGIS{'LOCAL_ID'},$HASH_KEGIS{'LOCAL_PASS'},\$TELNET,$TIMEOUTNUM,$PROMPT);
    if ( $ans != 0 )
    {
        return 1;
    }

    $TELNET->print("cd $TOOLDIR/Log");
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    my @dircheck = &ary_split(\@disp);
    foreach my $line (@dircheck)
    {
       	if ( $line =~ /No\ssuch\sfile\sor\sdirectory/ )
        { 
        	print TMPFILE "No such file or directory.\n";
        	return 1;
        }
    }
    
    $TELNET->print("find -type d -mtime +14");
    @disp = $TELNET->waitfor($PROMPT);
    print TMPFILE "@disp\n";
    print @disp;

    @disp_split = &ary_split(\@disp);
    foreach my $line (@disp_split)
    {
    	print "LOG:$line\n";
    	if($line =~ /^kcomserv02/ || $line =~ /^>/ || $line =~ /^\[/ || $line =~ /^find -type d -mtime \+14/ || $line =~ /^\$/)
    	{
    		#何もしない
    	}
    	else
    	{
    		$TELNET->print("rm -rf $line");
    		@disp = $TELNET->waitfor($PROMPT);
    		print TMPFILE "@disp\n";
    		print @disp;
    	}
    }  

    $TELNET->close;
}

################################################################################
# 関数名：ary_split                                                            #
# 概要  ：NetTelnet実行データについて取得したデータを                          #
#         改行で分割して１行ごとの配列データにする                             #
# 引数  ：１：分割元配列データ                                                 #
# 戻り値：分割後配列データ                                                     #
# グローバルへの書き込み：                                                     #
# 作成日:2022/09/28                                                            #
################################################################################
sub ary_split(\@)
{
    my $ary = shift;
    my @rtn_ary = ();

    foreach my $line ( @{$ary} )
    {	
        chomp($line);
        my @tmp = split(/\n/, $line);
        foreach my $data ( @tmp )
        {
            chomp($data);
            push(@rtn_ary,$data);
        }
    }

    return @rtn_ary;
}

################################################################################
# 関数名：ary_splitslash                                                          #
# 概要  ：filepathの’/’を分割してフォルダ名を一個ずっつ取得する                            #
# 引数  ：１：分割元配列データ                                                 #
# 戻り値：分割後配列データ                                                     #
# グローバルへの書き込み：                                                     #
# 作成日:2022/09/28                                                           #
################################################################################
sub ary_splitslash($)
{
    my $ary = shift;
    my @rtn_ary = ();


    my @tmp = split(/\//, $ary);
    foreach my $data ( @tmp )
    {
        chomp($data);
        push(@rtn_ary,$data);
    }

    return @rtn_ary;
}

################################################################################
# 関数名：connectlogtimer                                                      #
# 概要  ：connectログファイルへ時間を付与して書き込む                          #
# 引数  ：引数1:FTP or TELNET                                                  #
#         引数2:接続先サーバ                                                   #
#         引数3:処理状況                                                       #
# 戻り値：無し                                                                 #
# グローバルへの書き込み：無し                                                 #
# 作成日:2022/09/28                                                            #
################################################################################
sub connectlogtimer()
{
    my ($connect,$server,$flag)=@_;
    my ($sec,$min,$hour,$day,$mon,$year)=localtime(time);
    my $logtime=sprintf("%02d/%02d/%02d %02d:%02d:%02d",$year-100,$mon+1,$day,$hour,$min,$sec);
    print CONNECT "$logtime $connect $server $flag\n";
}

################################################################################
# 関数名：logcloseopen                                                         #
# 概要  ：ログファイルのCLOSEとOPENを行い、最新状態のログを保存する            #
# 引数  ：無し                                                                 #
# 戻り値：無し                                                                 #
# グローバルへの書き込み：無し                                                 #
# 作成日:2022/09/28                                                          #
################################################################################
sub logcloseopen($)
{
    close(CONNECT);
    close(TMPFILE);
    open(TMPFILE,">>$RESULTFILE");
    open(CONNECT,">>$CONNECTLOG");
}

###########################################################
# tool.confからデータを取得する
# 戻り値
# 0:正常
# 1:ファイル無
# 2:ファイルオープンエラー
# 作成日:2022/09/28 
###########################################################
sub get_tool_conf($\%)
{
    my $toolconf_file = shift;    # tool.confファイル名(フルパス)
    my $hash_toolconf = shift;    # 格納ハッシュアドレス

    if ( ! -f "$toolconf_file" )
    {
        return 1;
    }

    if ( ! open(IN,"$toolconf_file" ))
    {
        return 2;
    }

    while(my $line = <IN> )
    {
        $line =~ s/\x0D\x0A|\x0D|\x0A/\n/g;
    	chomp($line);
    	next if($line eq "");
        # "="で分割 項目名=値
        my @tmp = split(/=/, $line);
        # ハッシュに格納
        $hash_toolconf->{$tmp[0]} = $tmp[1];
    }
    close(IN);

    return 0;
}

###########################################################
# 日付取得
# 戻り値
#  日付データ
# 作成日:2022/09/28  
###########################################################
sub get_date()
{
    my $delay_sec = shift;
    my $format    = shift;
    my $ret = "";

    my ($sec,$min,$hour,$day,$mon,$year)=localtime(time);
    if ( $format eq "yyyymm" )
    {
        $ret = sprintf("%04d%02d",$year+1900,$mon+1);
    }
    elsif ( $format eq "yyyymmdd" )
    {
        $ret = sprintf("%04d%02d%02d",$year+1900,$mon+1,$day);
    }
    elsif ( $format eq "yyyymmddhhmmss" )
    {
        $ret = sprintf("%04d%02d%02d%02d%02d%02d",$year+1900,$mon+1,$day,$hour,$min,$sec);
    }
    elsif ( $format eq "yyyymmdd_hhmmss" )
    {
        $ret = sprintf("%04d%02d%02d_%02d%02d%02d",$year+1900,$mon+1,$day,$hour,$min,$sec);
    }
    elsif ( $format eq "yyyy-mm-dd hh:mm:ss" )
    {
        $ret = sprintf("%04d-%02d-%02d %02d:%02d:%02d",$year+1900,$mon+1,$day,$hour,$min,$sec);
    }

    return $ret;

}
