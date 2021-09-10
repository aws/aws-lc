#############################################################################
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License").
# You may not use this file except in compliance with the License.
# A copy of the License is located at
#
#  http://aws.amazon.com/apache2.0
#
# or in the "LICENSE" file accompanying this file. This file is distributed
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
# express or implied. See the License for the specific language governing
# permissions and limitations under the License.
#############################################################################

 ############################################################################
 #                         * * * NOTE * * *                                 #
 #                                                                          #
 # This is a primitive script to automate conversion of certain particular  #
 # x86 assembler files from Intel to AT&T syntax. It is *not* a general     #
 # conversion and is very tied to the specific limitations and conventions  #
 # in the intended targets. Even in that setting we only use it with an     #
 # additional sanity check that the object code generated is the same in    #
 # both original and translated code according to the GNU assembler.        #
 ############################################################################

s/\.intel_syntax *noprefix//

s/^(([a-z_0-9]+\:)* +[a-z_0-9]+ +)([^ (][^,/]*), *([^ ][^/,;\]*)([/;\].*)*$/\1\4, \3 \5/
s/^(([a-z_0-9]+\:)* +[a-z_0-9]+ +)([^ (][^,/]*), *([^ ][^/,]*), *([^ ][^/,;\]*)([/;\].*)*$/\1\5, \4, \3 \6/

s/ +,/,/

s/^([^/][^[]+)[[]([a-z_A-Z0-9]+) *\+ *8\*([a-z_A-Z0-9]+) *\+ *([a-z_A-Z0-9]+)[]]/\1\4\(\2,\3,8\)/
s/^([^/][^[]+)[[]([a-z_A-Z0-9]+) *\+ *8\*([a-z_A-Z0-9]+) *\- *([a-z_A-Z0-9]+)[]]/\1\-\4\(\2,\3,8\)/
s/^([^/][^[]+)[[]([a-z_0-9]+) *\+ *([A-Z0-9* ]+)[]]/\1\3\(\2\)/
s/^([^/][^[]+)[[]([a-z_0-9]+) *\- *([A-Z0-9* ]+)[]]/\1\-\3\(\2\)/
s/^([^/][^[]+)[[]([a-z_A-Z0-9]+) *\+ *8\*([a-z_A-Z0-9]+)[]]/\1\(\2,\3,8\)/
s/^([^/][^[]+)[[]([a-z_A-Z0-9]+) *\+ *([a-z_A-Z0-9]+)[]]/\1\(\2,\3\)/
s/^([^/][^[]+)[[]([^]]+)[]]/\1\(\2\)/

s/ cl$/ %cl/
s/ cl,/ %cl,/
s/([[(,.;: ])([re][abcd]x)/\1\%\2/g
s/([[(,.;: ])([re]sp)/\1\%\2/g
s/([[(,.;: ])([re]bp)/\1\%\2/g
s/([[(,.;: ])([re]si)/\1\%\2/g
s/([[(,.;: ])([re]di)/\1\%\2/g
s/([[(,.;: ])(r8d*)/\1\%\2/g
s/([[(,.;: ])(r9d*)/\1\%\2/g
s/([[(,.;: ])(r1[0-5]d*)/\1\%\2/g

s/^(([a-z_0-9]+\:)* +[a-z_0-9]+ +)([-~]*[0-9][A-Za-z0-9]* *\,)/\1$\3/
s/^(([a-z_0-9]+\:)* +[a-z_0-9]+ +)([-~]*[A-Z]* *\,)/\1$\3/

s/QWORD PTR//g

s/ adc  / adcq /g
s/ adcx  / adcxq /g
s/ add  / addq /g
s/ adox  / adoxq /g
s/ and  / andq /g
s/ bsf  / bsfq /g
s/ bsr  / bsrq /g
s/ bswap  / bswapq /g
s/ bt  / btq /g
s/ call  / callq /g
s/ cmovae  / cmovaeq /g
s/ cmovb  / cmovbq /g
s/ cmovc  / cmovcq /g
s/ cmove  / cmoveq /g
s/ cmovnc  / cmovncq /g
s/ cmovne  / cmovneq /g
s/ cmovnz  / cmovnzq /g
s/ cmovz  / cmovzq /g
s/ cmp  / cmpq /g
s/ dec  / decq /g
s/ imul  / imulq /g
s/ inc  / incq /g
s/ lea  / leaq /g
s/ mov  / movq /g
s/ movabs  / movabsq /g
s/ mul  / mulq /g
s/ mulx  / mulxq /g
s/ neg  / negq /g
s/ not  / notq /g
s/ or  / orq /g
s/ pop  / popq /g
s/ push  / pushq /g
s/ sar  / sarq /g
s/ sbb  / sbbq /g
s/ shl  / shlq /g
s/ shld  / shldq /g
s/ shr  / shrq /g
s/ shrd  / shrdq /g
s/ sub  / subq /g
s/ test  / testq /g
s/ xor  / xorq /g

s/q(  .*zeroe)/l\1/
s/q(  .*short)/l\1/
s/q(  .*%e)/l\1/
s/q(  .*%r[0-9]+d)/l\1/

s/ +$//
