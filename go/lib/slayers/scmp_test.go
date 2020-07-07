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

package slayers_test

import (
	"bytes"
	"net"
	"testing"

	"github.com/google/gopacket"
	"github.com/google/gopacket/layers"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/scionproto/scion/go/lib/slayers"
	"github.com/scionproto/scion/go/lib/xtest"
)

func TestSCMPDecodeFromBytes(t *testing.T) {
	testCases := map[string]struct {
		raw        []byte
		decoded    *slayers.SCMP
		assertFunc assert.ErrorAssertionFunc
	}{
		"valid": {
			raw: append([]byte{
				0x5, 0x0, 0x10, 0x92, // header
			}, bytes.Repeat([]byte{0xff}, 15)...), // payload
			decoded: &slayers.SCMP{
				TypeCode: slayers.CreateSCMPTypeCode(5, 0),
				Checksum: 4242,
			},
			assertFunc: assert.NoError,
		},
		"invalid small size": {
			raw:        []byte{0x5},
			decoded:    &slayers.SCMP{},
			assertFunc: assert.Error,
		},
	}

	for name, tc := range testCases {
		name, tc := name, tc
		t.Run(name, func(t *testing.T) {
			t.Parallel()
			got := &slayers.SCMP{}
			err := got.DecodeFromBytes(tc.raw, gopacket.NilDecodeFeedback)
			tc.assertFunc(t, err)
			if err != nil {
				return
			}
			tc.decoded.Contents = tc.raw[:4]
			tc.decoded.Payload = tc.raw[4:]
			assert.Equal(t, tc.decoded, got)
		})
	}
}

func TestSCMPSerializeTo(t *testing.T) {
	// scion header over which the pseudo checksum header is calculated.
	scnL := &slayers.SCION{
		DstIA: xtest.MustParseIA("1-ff00:0:4"),
	}
	err := scnL.SetDstAddr(&net.IPAddr{IP: net.ParseIP("174.16.4.1").To4()})
	assert.NoError(t, err)

	testCases := map[string]struct {
		raw        []byte
		decoded    *slayers.SCMP
		opts       gopacket.SerializeOptions
		assertFunc assert.ErrorAssertionFunc
	}{
		"valid": {
			raw: append([]byte{
				0x5, 0x0, 0x0, 0x0, // header
			}, bytes.Repeat([]byte{0xff}, 15)...), // payload
			decoded: &slayers.SCMP{
				TypeCode: slayers.CreateSCMPTypeCode(5, 0),
			},
			opts:       gopacket.SerializeOptions{ComputeChecksums: false},
			assertFunc: assert.NoError,
		},
		"valid with checksum": {
			raw: append([]byte{
				0x5, 0x0, 0x49, 0xe3, // header
			}, bytes.Repeat([]byte{0xff}, 15)...), // payload
			decoded: &slayers.SCMP{
				TypeCode: slayers.CreateSCMPTypeCode(5, 0),
			},
			opts:       gopacket.SerializeOptions{ComputeChecksums: true},
			assertFunc: assert.NoError,
		},
	}

	for name, tc := range testCases {
		name, tc := name, tc
		t.Run(name, func(t *testing.T) {
			t.Parallel()
			tc.decoded.Contents = tc.raw[:4]
			tc.decoded.Payload = tc.raw[4:]
			buffer := gopacket.NewSerializeBuffer()
			require.NoError(t, tc.decoded.SetNetworkLayerForChecksum(scnL))
			err := tc.decoded.SerializeTo(buffer, tc.opts)
			tc.assertFunc(t, err)
			if err != nil {
				return
			}
			assert.Equal(t, tc.raw[:len(tc.decoded.Contents)], buffer.Bytes())
		})
	}
}

func TestSCMP(t *testing.T) {
	testCases := map[string]struct {
		raw           []byte
		decodedLayers []gopacket.SerializableLayer
		opts          gopacket.SerializeOptions
		assertFunc    assert.ErrorAssertionFunc
	}{
		// "destination unreachable": {},
		// "packet too big":          {},
		// "parameter problem":       {},
		// "internal connectivity down": {},
		"external interface down": {
			raw: append([]byte{
				0x5, 0x0, 0x4a, 0xab, // header SCMP
				0x0, 0x1, 0xff, 0x0, // start header SCMP msg
				0x0, 0x0, 0x1, 0x11,
				0x0, 0x0, 0x0, 0x0,
				0x0, 0x0, 0x0, 0x5, // end  header SCMP msg
			}, bytes.Repeat([]byte{0xff}, 15)...), // final payload
			decodedLayers: []gopacket.SerializableLayer{
				&slayers.SCMP{
					BaseLayer: layers.BaseLayer{
						Contents: []byte{
							0x5, 0x0, 0x4a, 0xab, // header SCMP
						},
						Payload: append([]byte{
							0x0, 0x1, 0xff, 0x0,
							0x0, 0x0, 0x1, 0x11,
							0x0, 0x0, 0x0, 0x0,
							0x0, 0x0, 0x0, 0x5,
						}, bytes.Repeat([]byte{0xff}, 15)...),
					},
					TypeCode: slayers.CreateSCMPTypeCode(5, 0),
					Checksum: 19115,
				},
				&slayers.SCMPExternalInterfaceDown{
					BaseLayer: layers.BaseLayer{
						Contents: []byte{
							0x0, 0x1, 0xff, 0x0, // header SCMP msg
							0x0, 0x0, 0x1, 0x11,
							0x0, 0x0, 0x0, 0x0,
							0x0, 0x0, 0x0, 0x5,
						},
						Payload: bytes.Repeat([]byte{0xff}, 15),
					},
					IA:   xtest.MustParseIA("1-ff00:0:111"),
					IfID: uint64(5),
				},
				gopacket.Payload(bytes.Repeat([]byte{0xff}, 15)),
			},
			assertFunc: assert.NoError,
		},
	}

	for name, tc := range testCases {
		t.Run("decode", func(t *testing.T) {
			name, tc := name, tc
			t.Run(name, func(t *testing.T) {
				t.Parallel()
				packet := gopacket.NewPacket(tc.raw, slayers.LayerTypeSCMP, gopacket.Default)
				pe := packet.ErrorLayer()
				if pe != nil {
					require.NoError(t, pe.Error())
				}
				// Check that there are exactly X layers, e.g SCMP, SCMPMSG & Payload.
				require.Equal(t, len(tc.decodedLayers), len(packet.Layers()))

				for _, l := range tc.decodedLayers {
					switch v := l.(type) {
					case *slayers.SCMP:
						sl := packet.Layer(slayers.LayerTypeSCMP)
						require.NotNil(t, sl, "SCMP layer should exist")
						s := sl.(*slayers.SCMP)
						assert.Equal(t, v, s)
					case *slayers.SCMPExternalInterfaceDown:
						sl := packet.Layer(slayers.LayerTypeSCMPExternalInterfaceDown)
						require.NotNil(t, sl, "SCMPExternalInterfaceDown layer should exist")
						s := sl.(*slayers.SCMPExternalInterfaceDown)
						assert.Equal(t, v, s)
					case gopacket.Payload:
						sl := packet.Layer(gopacket.LayerTypePayload)
						require.NotNil(t, sl, "Payload should exist")
						s := sl.(*gopacket.Payload)
						assert.Equal(t, v.GoString(), s.GoString())
					default:
						assert.Fail(t, "all layers should match", "type %T", v)
					}
				}
				// TODO(karampok). it could give false positive if put SCMP/SCMP/PAYLOAD
				// assert.Empty(t, tc.decodedLayers, "all layers should have been tested")
			})
		})

		t.Run("serialize", func(t *testing.T) {
			scnL := &slayers.SCION{
				DstIA: xtest.MustParseIA("1-ff00:0:4"),
			}
			err := scnL.SetDstAddr(&net.IPAddr{IP: net.ParseIP("174.16.4.1").To4()})
			assert.NoError(t, err)

			for name, tc := range testCases {
				name, tc := name, tc
				t.Run(name, func(t *testing.T) {
					t.Parallel()
					opts := gopacket.SerializeOptions{ComputeChecksums: true}
					got := gopacket.NewSerializeBuffer()
					for _, l := range tc.decodedLayers {
						switch v := l.(type) {
						case *slayers.SCMP:
							require.NoError(t, v.SetNetworkLayerForChecksum(scnL))
						}
					}

					err := gopacket.SerializeLayers(got, opts, tc.decodedLayers...)
					require.NoError(t, err)
					assert.Equal(t, tc.raw, got.Bytes())
				})
			}
		})
	}
}