#!/bin/bash
printf '[Unit]\n  Description=/etc/rc.local Compatibility\n  ConditionPathExists=/etc/rc.local\n[Service]\n  Type=forking\n  ExecStart=/etc/rc.local start\n  TimeoutSec=0\n  StandardOutput=tty\n  RemainAfterExit=yes\n  SysVStartPriority=99\n\n[Install]\n  WantedBy=multi-user.target' | sudo tee -a /etc/systemd/system/rc-local.service
printf '#!/bin/bash\necho hi > hi.txt; aws s3 mv hi.txt s3://aws-lc-bm-framework-prod-bucket' | sudo tee -a /etc/rc.local
sudo chmod +x /etc/rc.local
sudo systemctl enable rc-local.service