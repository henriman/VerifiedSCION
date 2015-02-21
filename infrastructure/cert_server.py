# Copyright 2014 ETH Zurich

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

# http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""
:mod:`cert_server` --- SCION certificate server
===========================================
"""

from lib.packet.host_addr import IPv4HostAddr
from lib.packet.scion import (SCIONPacket, get_type, PacketType as PT,
    CertRequest, CertReply, TrcRequest, TrcReply, get_addr_from_type,
    get_cert_file_path)
from infrastructure.scion_elem import SCIONElement
from lib.packet.path import EmptyPath
import sys
import os
import logging
import base64


class CertServer(SCIONElement):
    """
    The SCION Certificate Server.
    """
    def __init__(self, addr, topo_file, config_file, trc_file):
        SCIONElement.__init__(self, addr, topo_file, config_file, trc_file)
        self.cert_requests = {}
        self.trc_requests = {}

    def _verify_cert(self, cert):
        """
        Verify certificate validity.
        """
        return True

    def _verify_trc(self, trc):
        """
        Verifiy TRC validity.
        """
        return True

    def process_cert_request(self, cert_req):
        """
        Process a certificate request
        """
        isinstance(cert_req, CertRequest)
        logging.info("Cert request received")
        src_addr = cert_req.hdr.src_addr
        ptype = get_type(cert_req)
        cert_file = get_cert_file_path(cert_req.cert_isd, cert_req.cert_ad,
            cert_req.cert_version)
        if not os.path.exists(cert_file):
            logging.info('Certificate not found.')
            self.cert_requests.setdefault((cert_req.cert_isd, cert_req.cert_ad,
                cert_req.cert_version), []).append(src_addr)
            new_cert_req = CertRequest.from_values(PT.CERT_REQ, self.addr,
                cert_req.ingress_if, cert_req.src_isd, cert_req.src_ad,
                cert_req.cert_isd, cert_req.cert_ad, cert_req.cert_version)
            dst_addr = self.ifid2addr[cert_req.ingress_if]
            self.send(new_cert_req, dst_addr)
            logging.info("New certificate request sent.")
        else:
            logging.info('Certificate found.')
            with open(cert_file, 'r') as file_handler:
                cert = file_handler.read()
            if not self._verify_cert(cert):
                logging.info("Certificate verification failed.")
                return
            cert_rep = CertReply.from_values(self.addr, cert_req.cert_isd,
                cert_req.cert_ad, cert_req.cert_version, cert)
            if ptype == PT.CERT_REQ_LOCAL:
                dst_addr = src_addr
            else:
                for router in self.topology.child_edge_routers:
                    if (cert_req.src_isd == router.interface.neighbor_isd and
                        cert_req.src_ad == router.interface.neighbor_ad):
                        dst_addr = router.addr
            self.send(cert_rep, dst_addr)
            logging.info("Certificate reply sent.")

    def process_cert_reply(self, cert_rep):
        """
        process a certificate reply
        """
        isinstance(cert_rep, CertReply)
        logging.info("Certificate reply received")
        if not self._verify_cert(cert_rep.cert):
            logging.info("Certificate verification failed.")
            return
        cert_file = get_cert_file_path(cert_rep.cert_isd, cert_rep.cert_ad,
            cert_rep.cert_version)
        if not os.path.exists(os.path.dirname(cert_file)):
            os.makedirs(os.path.dirname(cert_file))
        with open(cert_file, 'w') as file_handler:
            file_handler.write(cert_rep.cert)
        for dst_addr in self.cert_requests[(cert_rep.cert_isd, cert_rep.cert_ad,
            cert_rep.cert_version)]:
            new_cert_rep = CertReply.from_values(self.addr, cert_rep.cert_isd,
                cert_rep.cert_ad, cert_rep.cert_version, cert_rep.cert)
            self.send(new_cert_rep, dst_addr)
        del self.cert_requests[(cert_rep.cert_isd, cert_rep.cert_ad,
            cert_rep.cert_version)]
        logging.info("Certificate reply sent.")

    def process_trc_request(self, trc_req):
        """
        process a TRC request
        """
        isinstance(trc_req, TrcRequest)
        logging.info("TRC request received")
        src_addr = trc_req.hdr.src_addr
        path = trc_req.path
        if path is None:
            # TODO: ask PS
            # if still None: return
            pass
        trc_isd = trc_req.trc_isd
        trc_version = trc_req.trc_version
        trc_file = (ISD_DIR + trc_isd + '/ISD:' + trc_isd + '-V:' +
            trc_version + '.crt')
        if not os.path.exists(trc_file):
            logging.info('TRC file %s not found, sending up stream.', trc_isd)
            self.trc_requests.setdefault((trc_isd, trc_version),
                []).append(src_addr)
            dst_addr = get_addr_from_type(PT.TRC_REQ)
            new_trc_req = TrcRequest.from_values(PT.TRC_REQ, self.addr,
                dst_addr, path, trc_isd, trc_version)
            self.send(new_trc_req, dst_addr)
        else:
            logging.info('TRC file %s found, sending it back to requester (%s)',
                trc_isd, src_addr)
            with open(trc_file, 'r') as file_handler:
                trc = file_handler.read()
            if trc_req.hdr.path is None or trc_req.hdr.path == b'':
                trc_rep = TrcReply.from_values(self.addr, src_addr, None,
                    trc_isd, trc_version, trc)
                self.send(trc_rep, src_addr)
            else:
                path = path.reverse()
                trc_rep = TrcReply.from_values(self.addr, src_addr, path,
                    trc_isd, trc_version, trc)
                #trc_rep.hdr.set_downpath()
                (next_hop, port) = self.get_first_hop(trc_rep)
                logging.info("Sending TRC reply, using path: %s", path)
                self.send(trc_rep, next_hop, port)

    def process_trc_reply(self, trc_rep):
        """
        process a TRC reply
        """
        isinstance(trc_rep, TrcReply)
        logging.info("TRC reply received")
        trc_isd = trc_rep.trc_isd
        trc_version = trc_rep.trc_version
        trc = trc_rep.trc
        if not self._verify_cert(trc):
            logging.info("TRC verification failed.")
            return
        trc_file = (ISD_DIR + trc_isd + '/ISD:' + trc_isd + '-V:' +
            trc_version + '.crt')
        if not os.path.exists(os.path.dirname(trc_file)):
            os.makedirs(os.path.dirname(trc_file))
        with open(trc_file, 'w') as file_handler:
            file_handler.write(trc)
        for dst_addr in self.trc_requests[(trc_isd, trc_version)]:
            new_trc_rep = TrcReply.from_values(self.addr, dst_addr, None,
                trc_isd, trc_version, trc)
            self.send(new_trc_rep, dst_addr)
        del self.trc_requests[(trc_isd, trc_version)]

    def handle_request(self, packet, sender, from_local_socket=True):
        """
        Main routine to handle incoming SCION packets.
        """
        isinstance(packet, SCIONPacket)
        spkt = SCIONPacket(packet)
        ptype = get_type(spkt)
        if ptype == PT.CERT_REQ_LOCAL or ptype == PT.CERT_REQ:
            self.process_cert_request(CertRequest(packet))
        elif ptype == PT.CERT_REP:
            self.process_cert_reply(CertReply(packet))
        elif ptype == PT.TRC_REQ_LOCAL or ptype == PT.TRC_REQ:
            self.process_trc_request(TrcRequest(packet))
        elif ptype == PT.TRC_REP:
            self.process_trc_reply(TrcReply(packet))
        else:
            logging.info("Type not supported")

def main():
    """
    Main function.
    """
    logging.basicConfig(level=logging.DEBUG)
    if len(sys.argv) != 5:
        logging.info("run: %s IP topo_file conf_file trc_file", sys.argv[0])
        sys.exit()
    cert_server = CertServer(IPv4HostAddr(sys.argv[1]), sys.argv[2],
        sys.argv[3], sys.argv[4])
    cert_server.run()

if __name__ == "__main__":
    main()
