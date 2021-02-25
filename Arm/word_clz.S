/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

// ----------------------------------------------------------------------------
// Count leading zero bits in a single word
// Input a; output function return
//
//    extern uint64_t word_clz (uint64_t a);
//
// Standard ARM ABI: X0 = a, returns X0
// ----------------------------------------------------------------------------

.text
.globl word_clz

word_clz:
                clz     x0, x0
                ret
