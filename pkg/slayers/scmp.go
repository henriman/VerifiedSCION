// Copyright 2020 Anapaya Systems
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// +gobra

package slayers

import (
	"encoding/binary"
	"fmt"

	"github.com/google/gopacket"

	"github.com/scionproto/scion/pkg/private/serrors"
	// @ . "github.com/scionproto/scion/verification/utils/definitions"
	// @ sl "github.com/scionproto/scion/verification/utils/slices"
)

// MaxSCMPPacketLen the maximum length a SCION packet including SCMP quote can
// have. This length includes the SCION, and SCMP header of the packet.
//
//	+-------------------------+
//	|        Underlay         |
//	+-------------------------+
//	|          SCION          |  \
//	|          SCMP           |   \
//	+-------------------------+    \_ MaxSCMPPacketLen
//	|          Quote:         |    /
//	|        SCION Orig       |   /
//	|         L4 Orig         |  /
//	+-------------------------+
const MaxSCMPPacketLen = 1232

// SCMP is the SCMP header on top of SCION header.
//
//	 0                   1                   2                   3
//	 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|     Type      |     Code      |           Checksum            |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|                            InfoBlock                          |
//	+                                                               +
//	|                         (variable length)                     |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//	|                            DataBlock                          |
//	+                                                               +
//	|                         (variable length)                     |
//	+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
type SCMP struct {
	BaseLayer
	TypeCode SCMPTypeCode
	Checksum uint16

	scn *SCION
}

// LayerType returns LayerTypeSCMP.
// @ pure
// @ decreases
func (s *SCMP) LayerType() gopacket.LayerType {
	return LayerTypeSCMP
}

// CanDecode returns the set of layer types that this DecodingLayer can decode.
// @ ensures res != nil && res === LayerClassSCMP
// @ ensures typeOf(res) == gopacket.LayerType
// @ decreases
func (s *SCMP) CanDecode() (res gopacket.LayerClass) {
	// @ LayerClassSCMPIsLayerType()
	return LayerClassSCMP
}

// NextLayerType use the typecode to select the right next decoder.
// If the SCMP type is unknown, the next layer is gopacket.LayerTypePayload.
// NextLayerType returns the layer type contained by this DecodingLayer.
// @ requires acc(s.Mem(ub), R20) && s.IsLowDecodingLayer(true, ub)
// @ ensures  acc(s.Mem(ub), R20)
// @ decreases
func (s *SCMP) NextLayerType( /*@ ghost ub []byte @*/ ) gopacket.LayerType {
	// @ s.RevealIsLowDecodingLayer(true, ub, R20)
	switch /*@unfolding acc(s.Mem(ub), R20) in @*/ s.TypeCode.Type() {
	case SCMPTypeDestinationUnreachable:
		return LayerTypeSCMPDestinationUnreachable
	case SCMPTypePacketTooBig:
		return LayerTypeSCMPPacketTooBig
	case SCMPTypeParameterProblem:
		return LayerTypeSCMPParameterProblem
	case SCMPTypeExternalInterfaceDown:
		return LayerTypeSCMPExternalInterfaceDown
	case SCMPTypeInternalConnectivityDown:
		return LayerTypeSCMPInternalConnectivityDown
	case SCMPTypeEchoRequest, SCMPTypeEchoReply:
		return LayerTypeSCMPEcho
	case SCMPTypeTracerouteRequest, SCMPTypeTracerouteReply:
		return LayerTypeSCMPTraceroute
	}
	return gopacket.LayerTypePayload
}

// SerializeTo writes the serialized form of this layer into the
// SerializationBuffer, implementing gopacket.SerializableLayer.
// @ requires  b != nil
// @ requires  s.Mem(ubufMem) && s.IsLow(ubufMem)
// @ requires  low(opts.ComputeChecksums)
// @ requires  b.Mem() && sl.Bytes(b.UBuf(), 0, len(b.UBuf()))
// TODO[henri]: probably want to turn this into IsLow. Though I have no object for
// which to implement RevealIsLow ... could make this part of interface
// TODO: Once Gobra issue #846 is resolved, express this using `hyper` function
// (here and in the method body).
// @ requires  low(len(b.UBuf())) && 
// @ 	forall i int :: { sl.GetByte(b.UBuf(), 0, len(b.UBuf()), i) } 0 <= i && i < len(b.UBuf()) &&
// @ 		low(i) ==> low(sl.GetByte(b.UBuf(), 0, len(b.UBuf()), i))
// @ ensures   b.Mem() && sl.Bytes(b.UBuf(), 0, len(b.UBuf()))
// @ ensures   err == nil ==> s.Mem(ubufMem)
// @ ensures   err != nil ==> err.ErrorMem()
// @ decreases
func (s *SCMP) SerializeTo(b gopacket.SerializeBuffer, opts gopacket.SerializeOptions /*@, ghost ubufMem []byte @*/) (err error) {
	// @ s.RevealIsLowDecodingLayer(true, ubufMem, writePerm)
	bytes, err := b.PrependBytes(4)
	// @ underlyingBufRes := b.UBuf()
	if err != nil {
		return err
	}
	// TODO[henri]: minimize assertions
	// @ unfold acc(s.Mem(ubufMem), 1/2)
	// @ ghost if s.GetScn(true, ubufMem) != nil {
	// @ 	assert forall i int :: { s.GetScnRawSrcAddrByte(ubufMem, i) }{ s.scn.GetRawSrcAddrByte(i) } 0 <= i && i < s.scn.GetRawSrcAddrLen() ==>
	// @ 		s.GetScnRawSrcAddrByte(ubufMem, i) == s.scn.GetRawSrcAddrByte(i)
	// @ 	assert forall i int :: { s.GetScnRawDstAddrByte(ubufMem, i) }{ s.scn.GetRawDstAddrByte(i) } 0 <= i && i < s.scn.GetRawDstAddrLen() ==>
	// @ 		s.GetScnRawDstAddrByte(ubufMem, i) == s.scn.GetRawDstAddrByte(i)
	// @ }
	// @ unfold acc(s.Mem(ubufMem), 1/2)
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ unfold sl.Bytes(underlyingBufRes, 0, 2)
	// @ assert forall i int :: { &bytes[i] } 0 <= i && i < 2 ==> &bytes[i] == &underlyingBufRes[i]
	// @ fold sl.Bytes(bytes, 0, 2)
	// @ assert low(s.TypeCode)
	s.TypeCode.SerializeTo(bytes)
	// @ assert low(sl.GetByte(bytes, 0, 2, 0))
	// @ assert low(sl.GetByte(bytes, 0, 2, 1))
	// @ unfold sl.Bytes(bytes, 0, 2)
	// @ assert low(bytes[0])
	// @ assert low(bytes[1])
	// @ fold sl.Bytes(underlyingBufRes, 0, 2)
	// @ assert low(sl.GetByte(underlyingBufRes, 0, 2, 0))
	// @ assert low(sl.GetByte(underlyingBufRes, 0, 2, 1))
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 2, writePerm)
	// @ assert low(sl.GetByte(underlyingBufRes, 0, len(underlyingBufRes), 0))
	// @ assert low(sl.GetByte(underlyingBufRes, 0, len(underlyingBufRes), 1))

	//  assert low(len(underlyingBufRes)) &&
	//  	forall i int :: { sl.GetByte(underlyingBufRes, 0, len(underlyingBufRes), i) } 4 <= i && i < len(underlyingBufRes) &&
	//  		low(i) ==> low(sl.GetByte(underlyingBufRes, 0, len(underlyingBufRes), i))
	if opts.ComputeChecksums {
		if s.scn == nil {
			// @ fold s.Mem(ubufMem)
			return serrors.New("can not calculate checksum without SCION header")
		}
		// zero out checksum bytes
		// @ sl.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 4, writePerm)
		// @ assert low(sl.GetByte(underlyingBufRes, 0, 4, 0))
		// @ assert low(sl.GetByte(underlyingBufRes, 0, 4, 1))
		// @ unfold sl.Bytes(underlyingBufRes, 0, 4)
		// @ assert forall i int :: { &bytes[i] } 0 <= i && i < 4 ==> &bytes[i] == &underlyingBufRes[i]
		bytes[2] = 0
		bytes[3] = 0
		// @ assert low(bytes[0])
		// @ assert low(bytes[1])
		// @ assert low(bytes[2])
		// @ assert low(bytes[3])
		// @ fold sl.Bytes(underlyingBufRes, 0, 4)
		// @ assert low(sl.GetByte(underlyingBufRes, 0, 4, 0))
		// @ assert low(sl.GetByte(underlyingBufRes, 0, 4, 1))
		// @ assert low(sl.GetByte(underlyingBufRes, 0, 4, 2))
		// @ assert low(sl.GetByte(underlyingBufRes, 0, 4, 3))
		// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 4, writePerm)
		// @ assert low(sl.GetByte(underlyingBufRes, 0, len(underlyingBufRes), 0))
		// @ assert low(sl.GetByte(underlyingBufRes, 0, len(underlyingBufRes), 1))
		// @ assert low(sl.GetByte(underlyingBufRes, 0, len(underlyingBufRes), 2))
		// @ assert low(sl.GetByte(underlyingBufRes, 0, len(underlyingBufRes), 3))
		//  assert low(len(underlyingBufRes)) &&
		//  	forall i int :: { sl.GetByte(underlyingBufRes, 0, len(underlyingBufRes), i) } 4 <= i && i < len(underlyingBufRes) &&
		//  		low(i) ==> low(sl.GetByte(underlyingBufRes, 0, len(underlyingBufRes), i))
		//  assert forall i int :: { sl.GetByte(underlyingBufRes, 0, len(underlyingBufRes), i) } 0 <= i && i < 4 &&
		//  	low(i) ==> low(sl.GetByte(underlyingBufRes, 0, len(underlyingBufRes), i))
		verScionTmp := b.Bytes()
		//  assert low(len(verScionTmp)) &&
		//  	forall i int :: { sl.GetByte(verScionTmp, 0, len(verScionTmp), i) } 0 <= i && i < len(verScionTmp) &&
		//  		low(i) ==> low(sl.GetByte(verScionTmp, 0, len(verScionTmp), i))
		// @ unfold acc(s.scn.ChecksumMem(), 1/2)
		// @ assert forall i int :: { s.scn.GetRawSrcAddrByte(i) }{ sl.GetByte(s.scn.RawSrcAddr, 0, len(s.scn.RawSrcAddr), i) } 0 <= i && i < len(s.scn.RawSrcAddr) ==>
		// @ 	s.scn.GetRawSrcAddrByte(i) == sl.GetByte(s.scn.RawSrcAddr, 0, len(s.scn.RawSrcAddr), i)
		// @ assert forall i int :: { s.scn.GetRawDstAddrByte(i) }{ sl.GetByte(s.scn.RawDstAddr, 0, len(s.scn.RawDstAddr), i) } 0 <= i && i < len(s.scn.RawDstAddr) ==>
		// @ 	s.scn.GetRawDstAddrByte(i) == sl.GetByte(s.scn.RawDstAddr, 0, len(s.scn.RawDstAddr), i)
		// @ unfold acc(s.scn.ChecksumMem(), 1/2)
		s.Checksum, err = s.scn.computeChecksum(verScionTmp, uint8(L4SCMP))
		// @ fold s.scn.ChecksumMem()
		if err != nil {
			// @ fold s.Mem(ubufMem)
			return err
		}

	}
	// @ sl.SplitByIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 4, writePerm)
	// @ unfold sl.Bytes(underlyingBufRes, 0, 4)
	// @ assert forall i int :: { &bytes[i] } 0 <= i && i < 4 ==> &bytes[i] == &underlyingBufRes[i]
	// @ assert forall i int :: { &bytes[2:][i] } 0 <= i && i < 2 ==> &bytes[2:][i] == &bytes[i + 2]
	binary.BigEndian.PutUint16(bytes[2:], s.Checksum)
	// @ fold sl.Bytes(underlyingBufRes, 0, 4)
	// @ sl.CombineAtIndex_Bytes(underlyingBufRes, 0, len(underlyingBufRes), 4, writePerm)
	// @ fold s.Mem(ubufMem)
	return nil
}

// DecodeFromBytes decodes the given bytes into this layer.
// @ requires  s.NonInitMem() && s.IsLowDecodingLayer(false, nil)
// @ requires  df != nil
// @ requires  acc(sl.Bytes(data, 0, len(data)), R40)
// TODO: Once Gobra issue #846 is resolved, express this using `hyper` function.
// @ requires  low(len(data)) && 
// @ 	forall i int :: { sl.GetByte(data, 0, len(data), i) } 0 <= i && i < len(data) &&
// @ 		low(i) ==> low(sl.GetByte(data, 0, len(data), i))
// @ preserves df.Mem()
// @ ensures   acc(sl.Bytes(data, 0, len(data)), R40)
// @ ensures   res == nil ==> s.Mem(data)
// @ ensures   res != nil ==> (s.NonInitMem() && res.ErrorMem())
// @ ensures   low(res != nil)
// @ ensures   res == nil ==> 
// @ 	old(s.GetScn(false, nil)) == nil ==> s.IsLowDecodingLayer(true, data)
// @ decreases
func (s *SCMP) DecodeFromBytes(data []byte, df gopacket.DecodeFeedback) (res error) {
	// TODO[henri]: minimize assertions
	// @ assert s.GetScn(false, nil) == old(s.GetScn(false, nil))
	// @ s.RevealIsLowDecodingLayer(false, nil, HalfPerm)
	if size := len(data); size < 4 {
		df.SetTruncated()
		return serrors.New("SCMP layer length is less then 4 bytes", "minimum", 4, "actual", size)
	}
	// @ assert s.GetScn(false, nil) == old(s.GetScn(false, nil))
	// @ unfold s.NonInitMem()
	// @ assert s.scn == old(s.GetScn(false, nil))
	// @ requires len(data) >= 4
	// @ requires acc(sl.Bytes(data, 0, len(data)), R40)
	// @ requires low(sl.GetByte(data, 0, len(data), 0)) && low(sl.GetByte(data, 0, len(data), 1))
	// @ preserves acc(&s.TypeCode)
	// @ ensures acc(sl.Bytes(data, 2, len(data)), R40)
	// @ ensures acc(sl.Bytes(data, 0, 2), R40)
	// @ ensures low(s.TypeCode)
	// @ decreases
	// @ outline (
	// @ sl.SplitByIndex_Bytes(data, 0, len(data), 2, R40)
	// @ unfold acc(sl.Bytes(data, 0, 2), R41)
	// @ assert sl.GetByte(data, 0, 2, 0) == data[0]
	// @ assert sl.GetByte(data, 0, 2, 1) == data[1]
	s.TypeCode = CreateSCMPTypeCode(SCMPType(data[0]), SCMPCode(data[1]))
	// @ fold acc(sl.Bytes(data, 0, 2), R41)
	// @ )
	// @ assert s.scn == old(s.GetScn(false, nil))
	// @ requires len(data) >= 4
	// @ requires acc(sl.Bytes(data, 0, 2), R40)
	// @ requires acc(sl.Bytes(data, 2, len(data)), R40)
	// @ preserves acc(&s.Checksum)
	// @ ensures acc(sl.Bytes(data, 0, len(data)), R40)
	// @ decreases
	// @ outline (
	// @ sl.SplitByIndex_Bytes(data, 2, len(data), 4, R40)
	// @ unfold acc(sl.Bytes(data, 2, 4), R40)
	// @ assert forall i int :: { &data[2:4][i] } 0 <= i && i < 2 ==> &data[2 + i] == &data[2:4][i]
	s.Checksum = binary.BigEndian.Uint16(data[2:4])
	// @ fold acc(sl.Bytes(data, 2, 4), R40)
	// @ sl.CombineAtIndex_Bytes(data, 0, 4, 2, R40)
	// @ sl.CombineAtIndex_Bytes(data, 0, len(data), 4, R40)
	// @ )
	// @ assert s.scn == old(s.GetScn(false, nil))
	s.BaseLayer = BaseLayer{Contents: data[:4], Payload: data[4:]}
	// @ fold s.BaseLayer.Mem(data, 4)
	// @ assert low(s.TypeCode)
	// @ assert s.scn == old(s.GetScn(false, nil))
	// @ fold s.Mem(data)
	// @ assert s.GetScn(true, data) == old(s.GetScn(false, nil))
	// @ assert low(s.GetTypeCode(true, data))
	// @ ghost if s.GetScn(true, data) == nil {
	// @ 	s.AssertIsLow(true, data, writePerm)
	// @ }
	return nil
}

// @ requires s != nil
// @ preserves acc(&s.TypeCode) && acc(&s.Checksum) && acc(&s.Payload) && acc(s.Payload)
// @ decreases
func (s *SCMP) String() string {
	return fmt.Sprintf("%s(%d)\nPayload: %s", &s.TypeCode, s.Checksum, s.Payload)
}

// SetNetworkLayerForChecksum tells this layer which network layer is wrapping it.
// This is needed for computing the checksum when serializing,
// @ preserves acc(&s.scn)
// @ ensures   s.scn == scn
// @ decreases
func (s *SCMP) SetNetworkLayerForChecksum(scn *SCION) {
	s.scn = scn
}

// @ requires  pb != nil
// @ requires  sl.Bytes(data, 0, len(data))
// TODO: Once Gobra issue #846 is resolved, express this using `hyper` function.
// @ requires  low(len(data)) && 
// @ 	forall i int :: { sl.GetByte(data, 0, len(data), i) } 0 <= i && i < len(data) &&
// @ 		low(i) ==> low(sl.GetByte(data, 0, len(data), i))
// @ preserves pb.Mem()
// @ ensures   res != nil ==> res.ErrorMem()
// @ decreases
func decodeSCMP(data []byte, pb gopacket.PacketBuilder) (res error) {
	scmp := &SCMP{}
	// @ fold scmp.NonInitMem()
	// TODO[henri]: minimize assertions
	// @ assert scmp.GetScn(false, nil) == nil
	// @ scmp.AssertIsLow(false, nil, HalfPerm)
	// @ assert scmp.GetScn(false, nil) == nil
	err := scmp.DecodeFromBytes(data, pb)
	if err != nil {
		return err
	}
	pb.AddLayer(scmp)
	verScionTmp := scmp.NextLayerType( /*@ data @*/ )
	// @ fold verScionTmp.Mem()
	return pb.NextDecoder(verScionTmp)
}
