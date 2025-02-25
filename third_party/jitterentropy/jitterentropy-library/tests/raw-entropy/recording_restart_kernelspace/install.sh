#!/bin/bash

#	Install the linux kernel and the service running the boottime test

# Note: restorecon is needed for Fedora 
if [ ! -x /usr/local/sbin/getrawentropy ];
then
	echo "getrawentropy must be installed in /usr/local/sbin"
	exit 1
fi

cp boottime_test_record.sh /usr/local/sbin/ &&
chmod u+x /usr/local/sbin/boottime_test_record.sh &&
cp boottime_test_record.service /etc/systemd/system/ &&
systemctl enable boottime_test_record &&
restorecon -v -R /

echo "To improve the reboot speed change the timeout in /etc/default/grub as follows"
echo "GRUB_TIMEOUT=1"
echo "Then run grub2-mkconfig to update the grub configuration file for the new setting to take effect."
