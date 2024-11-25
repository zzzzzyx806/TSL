# 介绍
该项目使用了ECDSA 曲线和 AES 加密进行安全客户端通信的示例。该示例通过加载客户端证书和私钥与服务器建立加密连接，进行密钥协商并使用生成的 AES 密钥加密和解密数据。

## 具体过程
1. 使用 SSL/TLS 与服务器建立加密连接。
2. 通过 ECDSA 曲线生成私钥并计算共享密钥。
3. 使用共享密钥生成 AES 密钥并加密数据。
4. 加密的数据发送到服务器后，客户端接收并解密响应数据。

## 安装依赖
运行此代码之前，请确保安装了以下 Python 库：
- `pycryptodome` - 用于 AES 加密。
- `ecdsa` - 用于 ECDSA 曲线和密钥生成。
- `ssl` - 用于 SSL/TLS 安全连接。
- `socket` - 用于网络通信

使用时需要生成一个客户端证书和私钥。你可以使用 OpenSSL 来生成自签名证书和私钥。

## 代码说明
load_client_cert(cert_file, key_file)  加载客户端证书和私钥。
create_secure_connection(host, port, context)  创建与服务器的 SSL/TLS 加密连接。
generate_private_key(n)  生成私钥。
generate_aes_key(shared_key)  基于共享密钥生成 AES 密钥。
encrypt_data(aes_key, data)  使用 AES 加密数据。
decrypt_data(aes_key, data)  使用 AES 解密数据。
