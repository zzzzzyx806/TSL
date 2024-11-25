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

# 生成密钥对 (私钥 d 和公钥 V)
def generate_keypair():
    d = random.randint(1, n-1)  # 私钥 d
    V = point_multiply(d, G)    # 公钥 V = d * G
    return d, V

# 签名过程
def sign_message(private_key, message):
    e = sha256(message.encode('utf-8')).digest()
    e = int.from_bytes(e, byteorder='big')  # 将消息哈希值转换为整数
    k = random.randint(1, n-1)  # 随机数 k
    R = point_multiply(k, G)   # 计算点 R = k * G
    r = R[0] % n  # r 是 R 的 x 坐标模 n
    s = (mod_inverse(k, n) * (e + private_key * r)) % n  # s 的计算公式
    return r, s

# 验证过程
def verify_signature(public_key, message, signature):
    r, s = signature
    if r <= 0 or s <= 0 or r >= n or s >= n:
        return False  # 签名不合法

    e = sha256(message.encode('utf-8')).digest()
    e = int.from_bytes(e, byteorder='big')  # 将消息哈希值转换为整数

    w = mod_inverse(s, n)
    u1 = (e * w) % n
    u2 = (r * w) % n
    P = point_add(point_multiply(u1, G), point_multiply(u2, public_key))  # P = u1 * G + u2 * V
    return r == P[0] % n  # 验证 r 是否匹配

# 使用 GM 加密的函数
def gm_encrypt(public_key, message):
    N, a = public_key
    
    # 选择明文 m，可能为 0 或 1
    m = 0 if message == '0' else 1
    
    # 随机选择一个整数 r，满足 1 < r < N
    r = random.randint(2, N - 1)
    
    # 计算密文 c
    r_square = pow(r, 2, N)  # 计算 r^2 % N
    
    if m == 0:
        c = r_square
    else:
        c = (a * r_square) % N
    
    return c

# 建立安全连接
def create_secure_connection(host, port, context):
    connection = context.wrap_socket(socket.socket(socket.AF_INET), server_hostname=host)
    connection.connect((host, port))
    return connection

# 生成私钥 (DH)
def generate_private_key(p):
    while True:
        private_key = random.randint(1, p - 1)
        if private_key > 0:
            return private_key

# 计算公钥
def generate_public_key(private_key, g, p):
    return pow(g, private_key, p)

# 计算共享密钥
def calculate_shared_key(public_key, private_key, p):
    return pow(public_key, private_key, p)

# Alice 和 Bob 的 DH 密钥交换过程
def dh_key_exchange():
    # Alice 的私钥和公钥
    alice_private_key = generate_private_key(p)
    alice_public_key = generate_public_key(alice_private_key, g, p)

    # Bob 的私钥和公钥
    bob_private_key = generate_private_key(p)
    bob_public_key = generate_public_key(bob_private_key, g, p)

    # 交换公钥：Alice 将公钥发送给 Bob，Bob 将公钥发送给 Alice
    # Alice 使用 Bob 的公钥计算共享密钥
    alice_shared_key = calculate_shared_key(bob_public_key, alice_private_key, p)
    
    # Bob 使用 Alice 的公钥计算共享密钥
    bob_shared_key = calculate_shared_key(alice_public_key, bob_private_key, p)

    assert alice_shared_key == bob_shared_key, "共享密钥不一致!"

    return alice_shared_key  # 返回共享密钥

# 生成 AES 密钥
def generate_aes_key(shared_key):
    # 将共享密钥转换为字节并取前 32 字节
    return shared_key.to_bytes(32, byteorder='big')

def is_text_file(file_path):
    text_extensions = ['.txt', '.csv', '.json', '.xml']
    _, ext = os.path.splitext(file_path)
    return ext in text_extensions

def encrypt_message(message, server_public_key, client_private_key):
    # 首先，进行 DH 密钥交换以获取共享密钥
    shared_key = dh_key_exchange()

    # 使用 DH 生成的共享密钥生成 AES 密钥
    aes_key = generate_aes_key(shared_key)

    # 判断消息类型并选择合适的加密方式
    if isinstance(message, str):
        if len(message) < 100:
            print("Using GM encryption for text message...") 
            encrypted_message = gm_encrypt(server_public_key, message)
        else:
            print("Using AES encryption for long text message...")
            encrypted_message = encrypt_data(aes_key, message)
    elif isinstance(message, bytes):
        print("Using AES encryption for binary file message...")
        encrypted_message = encrypt_data(aes_key, message)
    else:
        raise ValueError("Unsupported message type")
    
    return encrypted_message

# 文件加密
def encrypt_file(file_path, server_public_key, client_private_key):
    with open(file_path, 'rb') as f:
        file_data = f.read()

    if is_text_file(file_path):
        print("Using GM encryption for text file...")
        encrypted_data = gm_encrypt(server_public_key, file_data.decode())
    else:
        print("Using AES encryption for binary file...")
        aes_key = generate_aes_key(client_private_key)
        encrypted_data = encrypt_data(aes_key, file_data)
    
    return encrypted_data

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

def encrypt_block(block_data, key):
    return encrypt_data(key, block_data)

# 异步加密多个文件
async def encrypt_files_async(file_paths, server_public_key, client_private_key):
    """
    异步加密多个文件
    """
    loop = asyncio.get_event_loop()
    tasks = []

    # 使用线程池加速文件加密
    with ThreadPoolExecutor() as executor:
        for file_path in file_paths:
            tasks.append(loop.run_in_executor(executor, encrypt_file, file_path, server_public_key, client_private_key))
        
        encrypted_files = await asyncio.gather(*tasks)
    
    return encrypted_files

# 批量加密文件
def batch_encrypt_files(file_paths, aes_key):
    """
    批量加密多个文件
    """
    encrypted_files = []
    
    for file_path in file_paths:
        with open(file_path, 'rb') as f:
            file_data = f.read()

        encrypted_file = encrypt_data(aes_key, file_data)
        encrypted_files.append(encrypted_file)
    
    return encrypted_files

def encrypt_file(file_path, server_public_key, client_private_key):
    with open(file_path, 'rb') as f:
        file_data = f.read()

    if is_text_file(file_path):
        print(f"Using GM encryption for text file: {file_path}")
        encrypted_data = gm_encrypt(server_public_key, file_data.decode())
    else:
        print(f"Using AES encryption for binary file: {file_path}")
        aes_key = generate_aes_key(client_private_key)
        encrypted_data = encrypt_data(aes_key, file_data)

    return encrypted_data

# 检查是否是文本文件
def is_text_file(file_path):
    # 简单示例：如果文件以.txt结尾，则认为是文本文件
    return file_path.endswith('.txt')

# 异步加密多个文件
async def encrypt_files_async(file_paths, server_public_key, client_private_key):
    loop = asyncio.get_event_loop()
    tasks = []

    # 使用线程池加速文件加密
    with ThreadPoolExecutor() as executor:
        for file_path in file_paths:
            tasks.append(loop.run_in_executor(executor, encrypt_file, file_path, server_public_key, client_private_key))
        
        encrypted_files = await asyncio.gather(*tasks)
    
    return encrypted_files

# 批量加密文件
def batch_encrypt_files(file_paths, aes_key):
    encrypted_files = []
    
    for file_path in file_paths:
        with open(file_path, 'rb') as f:
            file_data = f.read()

        encrypted_file = encrypt_data(aes_key, file_data)
        encrypted_files.append(encrypted_file)
    
    return encrypted_files

# 客户端-服务器通信
def perform_authentication(client_private_key, server_public_key, connection):
    # 模拟身份验证过程
    pass  # 这里需要实际的认证逻辑

async def main():
    # 创建客户端的 ECDSA 密钥对
    client_private_key, client_public_key = generate_keypair()  # 使用你定义的生成密钥对函数
    print(f"Client public key: {client_public_key}")

    # 创建 socket 连接
    host = 'localhost'
    port = 10000
    connection = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    connection.connect((host, port))

    # 执行身份验证
    server_public_key = None  # 假设你从服务器获取的公钥
    await perform_authentication(client_private_key, server_public_key, connection)

    # 上传要加密的消息
    message = "Hello, Server!"  # 这可以是一个文本或更复杂的数据（如文件）

    # 判断消息类型，选择加密方法
    if isinstance(message, str):
        if len(message) < 100:  # 根据消息长度决定加密方式
            print("Using GM encryption for short message...")
            encrypted_message = encrypt_message(message, server_public_key, client_private_key)
        else:
            print("Using AES encryption for long message...")
            encrypted_message = encrypt_message(message, server_public_key, client_private_key)  # 这里直接调用加密函数
    elif isinstance(message, bytes):
        print("Using AES encryption for binary file message...")
        encrypted_message = encrypt_message(message, server_public_key, client_private_key)  # 这里也调用 AES 加密
    else:
        raise ValueError("Unsupported message type")

    # 上传加密的数据
    await upload_encrypted_data(connection, encrypted_message, server_public_key, client_private_key)

    # 接收并解密响应
    decrypted_message = receive_and_decrypt_data(connection, client_private_key)
    print(f"Received decrypted message: {decrypted_message}")

    # 关闭连接
    connection.close()

# 运行异步代码
asyncio.run(main())
