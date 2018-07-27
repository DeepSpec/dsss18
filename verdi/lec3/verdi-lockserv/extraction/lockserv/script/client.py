import socket
import re
from struct import pack, unpack

class SendError(Exception):
    pass

class ReceiveError(Exception):
    pass

class Client(object):
    re_locked = re.compile(r'Locked')

    def __init__(self, host, port, sock=None):
        if not sock:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.sock.connect((host, port))
        else:
            self.sock = sock

    def send_msg(self, msg):
        n = self.sock.send(pack("<I", len(msg)))
        if n < 4:
            raise SendError
        else:
            self.sock.send(msg)

    def recv_msg(self, re):
        len_bytes = self.sock.recv(4)
        if len_bytes == '':
            raise ReceiveError
        else:
            len = unpack("<I", len_bytes)[0]
            data = self.sock.recv(len)
            if data == '':
                raise ReceiveError
            else:
                return self.parse_response(data, re)

    def send_lock(self):
        self.send_msg('Lock')
        return self.recv_msg(self.re_locked)

    def send_unlock(self):
        self.send_msg('Unlock')

    def parse_response(self, data, re):
        try:
            if re.match(data):
                return 'Locked'
            else:
                return None
        except Exception as e:
            print "Parse error, data=%s" % data
            raise e
