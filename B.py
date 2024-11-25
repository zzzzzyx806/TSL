from Crypto.Cipher import AES
from Crypto.Random import get_random_bytes
from ecdsa.ellipticcurve import Point
from ecdsa import SigningKey, VerifyingKey, SECP521r1
from ecdsa.util import sigencode_string, sigdecode_string
import socket
import hashlib
import time
import json
import os
import asyncio
from concurrent.futures import ThreadPoolExecutor
from Crypto.PublicKey import ElGamal
import random
from sympy import mod_inverse,isprime

p = 0x1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
n = 0x1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE5FB1A724DC8021C2407A7AFC3D03C4B7DDAF5D578C67D6FBBCE4726F73C60E
a = -3
b = 0x5CF9B44A861E121DB5068C6F04E803FB9EAFD9E27B6592B627E7DCA71A6B51B0011A2EFB0D2761B96F0F1D27D56C2BC56
G = (0xC1F23C9B97139C4D0C0C38B5D810FCA2425FF567D4847C1065457FE3DAABF7B7229EF6A26E24A42E2E4A3D6E2BCF3A34, 0x380B44C1219C510C2D36E9DBB556A699F97B1C6B72F4B0E574C8B6C4BE65E2B6729E73B78F6C11816328C2C5E2694E8F)
# G 是曲线的生成点（基点），具体数值为标准化值

# 曲线加法函数 (点加法)
def point_add(P, Q):
    # P = (x1, y1), Q = (x2, y2)
    if P == (0, 0):  # 点P是无穷远点时返回 Q
        return Q
    if Q == (0, 0):  # 点Q是无穷远点时返回 P
        return P

    x1, y1 = P
    x2, y2 = Q
    # 计算斜率 lambda
    if P == Q:  # P == Q 时的切线斜率公式
        lam = ((3 * x1 * x1 + a) * mod_inverse(2 * y1, p)) % p
    else:  # P != Q 时的斜率公式
        lam = ((y2 - y1) * mod_inverse(x2 - x1, p)) % p

    # 计算新的点 (x3, y3)
    x3 = (lam * lam - x1 - x2) % p
    y3 = (lam * (x1 - x3) - y1) % p

    return (x3, y3)

# 曲线点乘函数 (标量乘法)
def point_multiply(k, P):
    result = (0, 0)  # 无穷远点
    addend = P

    while k > 0:
        if k % 2 == 1:
            result = point_add(result, addend)
        addend = point_add(addend, addend)
        k = k // 2

    return result

# 模逆计算
def mod_inverse(x, p):
    """计算 x 在模 p 下的逆元"""
    return pow(x, p - 2, p)  # 使用费马小定理计算逆元

# 签名过程
def sign_message(private_key, message):
    e = sha256(message.encode('utf-8')).digest()
    e = int.from_bytes(e, byteorder='big')  # 将消息哈希值转换为整数
    k = random.randint(1, n-1)  # 随机数 k
    R = point_multiply(k, G)   # 计算点 R = k * G
    r = R[0] % n  # r 是 R 的 x 坐标模 n
    s = (mod_inverse(k, n) * (e + private_key * r)) % n  # s 的计算公式
    return r, s

# 签名验证过程
def verify_signature(r, s, M, V):
    H_m = M  # 假设消息已散列
    if not (0 < r < n and 0 < s < n):
        return False

    s_inv = mod_inverse(s, n)
    u1 = (H_m * s_inv) % n
    u2 = (r * s_inv) % n

    P = point_add(point_multiply(u1, G), point_multiply(u2, V))

    if P == (0, 0):
        return False

    x_P, y_P = P
    return r == x_P % n

def perform_authentication(client_private_key, server_public_key, connection):
    # 客户端生成签名
    nonce = str(time.time()).encode()  # 使用当前时间戳作为消息
    client_signature = generate_signature(client_private_key, nonce)
    client_public_key = client_private_key.get_verifying_key()

    # 发送公钥、签名和消息给服务器
    auth_data = json.dumps({
        "public_key": client_public_key.to_string().hex(),
        "nonce": nonce.decode(),
        "signature": client_signature.hex(),
    }).encode()
    connection.sendall(auth_data)

    # 接收服务器的签名验证结果
    server_response = json.loads(connection.recv(1024).decode())
    if server_response.get("status") == "success":
        print("Server authentication successful!")
    else:
        raise Exception("Server authentication failed!")

    # 在身份验证成功后，A端生成自己的签名，回复给服务器
    server_nonce = server_response["nonce"].encode()  # 获取服务器的nonce
    server_signature = server_response["signature"]
    # 验证服务器的签名
    if verify_signature(server_public_key, server_nonce, bytes.fromhex(server_signature)):
        print("Server signature verification successful!")
    else:
        print("Server signature verification failed!")

        
def generate_keys(bits=512):
    # 选择两个大素数 p 和 q
    p = q = 1
    while not isprime(p):
        p = random.getrandbits(bits)
    while not isprime(q):
        q = random.getrandbits(bits)
    N = p * q
    # 选择一个整数 a，满足 a 不是 p 和 q 模意义下的二次剩余
    a = 1
    while True:
        a = random.randint(2, N)
        if pow(a, (p - 1) // 2, p) != 1 and pow(a, (q - 1) // 2, q) != 1:
            break
    public_key = (N, a)
    private_key = (p, q)
    return public_key, private_key

def gm_decrypt(private_key, ciphertext):
    p, q = private_key
    N = p * q

    # 解密过程
    c = ciphertext
    
    # 计算 c 的二次剩余判定
    root_c = pow(c, (p + 1) // 4, p)  # 求 c 的二次剩余平方根 mod p
    root_q = pow(c, (q + 1) // 4, q)  # 求 c 的二次剩余平方根 mod q
    
    # 使用中国剩余定理恢复根
    m = (root_c * root_q) % N
    
    # 判断 m 的值
    if m == 0:
        return '0'
    elif m == 1:
        return '1'
    else:
        return 'Error'


# 建立安全连接
def create_secure_server_socket(host, port, context):
    server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server_socket.bind((host, port))
    server_socket.listen(5)
    print(f"Server listening on {host}:{port}")
    
    secure_socket = context.wrap_socket(server_socket, server_side=True)
    connection, address = secure_socket.accept()
    print(f"Connection from {address}")
    return connection

# 生成 AES 密钥
def generate_aes_key(shared_key):
    return shared_key.x.to_bytes(32, byteorder='big')

# 加密数据
def encrypt_data(aes_key, data):
    cipher = AES.new(aes_key, AES.MODE_GCM)
    ciphertext, tag = cipher.encrypt_and_digest(data.encode())
    return cipher.nonce + tag + ciphertext

# 解密数据
def decrypt_data(aes_key, data):
    nonce, tag, ciphertext = data[:16], data[16:32], data[32:]
    cipher = AES.new(aes_key, AES.MODE_GCM, nonce=nonce)
    return cipher.decrypt_and_verify(ciphertext, tag).decode()

# 计算共享密钥
def compute_shared_key(private_key, public_key):
    return private_key * public_key

def main():
    # 创建与客户端的安全连接
    connection = create_secure_server_socket(host, port, context)
    
    # 获取客户端加密方式的选择（例如 GM 或 AES）
    encryption_method = connection.recv(1024).decode()  # 例如：'AES' 或 'GM'
    
    # 创建曲线和生成私钥
    curve = SECP521r1.curve
    n = curve.order
    G = SECP521r1.generator
    n_B = get_random_bytes(66)  # 生成私钥
    n_B = int.from_bytes(n_B, 'big') % n
    Q_B = n_B * G
    
    # 发送 B 端的公钥给客户端
    connection.sendall(Q_B.to_bytes(66, 'big'))  # 发送公钥
    
    # 接收客户端发送的加密数据
    encrypted_data = connection.recv(1024)
    
    # 获取客户端发送的公钥 Q_A
    Q_A_from_A = Point(curve, int.from_bytes(encrypted_data[:66], 'big'), 0)
    
    # 计算共享密钥
    shared_key = compute_shared_key(n_B, Q_A_from_A)
    
    # 使用共享密钥生成 AES 密钥
    aes_key = generate_aes_key(shared_key)
    
    # 根据加密方式进行解密
    if encryption_method == 'AES':
        decrypted_message = decrypt_data(aes_key, encrypted_data[66:])
    elif encryption_method == 'GM':
        decrypted_message = gm_decrypt(shared_key, encrypted_data[66:])
    else:
        raise Exception("Unsupported encryption method")
    
    print(f"Received decrypted message: {decrypted_message}")
    
    # 对响应消息进行加密并发送给客户端
    response_message = 'Hello, Client!'
    
    if encryption_method == 'AES':
        encrypted_response = encrypt_data(aes_key, response_message)
    elif encryption_method == 'GM':
        encrypted_response = gm_encrypt(shared_key, response_message)  # GM 加密的实现需要补充
    
    connection.sendall(encrypted_response)
    
    # 关闭连接
    connection.close()
